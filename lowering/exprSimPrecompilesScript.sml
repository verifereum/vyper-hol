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
  cheat
QED

Theorem padded_num_to_be_bytes:
  !k n. n < 256 ** k ==>
    PAD_LEFT 0w k (num_to_be_bytes n) = REVERSE (bytes_of_num k n)
Proof
  cheat
QED

Theorem padded_num_to_be_bytes_word32:
  n < 2 ** 256 ==>
  PAD_LEFT 0w 32 (num_to_be_bytes n) = word_to_bytes (n2w n:bytes32) T
Proof
  cheat
QED

Theorem write_memory_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= dst \/ dst + LENGTH data <= b) /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (write_memory_with_expansion dst data s) ==>
  stmt_state_rel ctx func cenv cx es (write_memory_with_expansion dst data s)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem computed_static_empty_probe[local]:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ s.vs_outcomes = [] ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 0w
      ((write_memory_with_expansion (w2n ro) [] s)
        with <|vs_returndata := []; vs_outcomes := []|>))
Proof
  cheat
QED

Theorem computed_static_false_probe[local]:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\ s.vs_outcomes = head::rest /\ ~head.co_success ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out 0w
      ((write_memory_with_expansion (w2n ro) [] s)
        with <|vs_returndata := []; vs_outcomes := rest|>))
Proof
  cheat
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
  cheat
QED

Theorem ecrecover_typing[local]:
  well_typed_builtin_app ty ECRecover ts ==>
  LENGTH ts = 4 /\ ty = BaseT AddressT /\
  HD ts = BaseT (BytesT (Fixed 32)) /\
  (EL 1 ts = BaseT (UintT 8) \/ EL 1 ts = BaseT (UintT 256) \/
   EL 1 ts = BaseT (BytesT (Fixed 32))) /\
  EVERY (\t. t = BaseT (UintT 256) \/ t = BaseT (BytesT (Fixed 32))) (TL (TL ts))
Proof
  cheat
QED

Theorem expr_post_typed_stack_operand:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  cheat
QED

Theorem expr_post_typed_stack_intro:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  stmt_state_rel ctx func cenv cx es' s /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  wb_frame cenv es sa s0 s ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  cheat
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
  cheat
QED

Theorem typed_args_ready_tail:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
  typed_args_ready ctx func cenv cx arg_ty Inv args
Proof
  cheat
QED

Theorem typed_args_cons_cases:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  eval_exprs cx (e::args) es = (res, es') ==>
  (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc, es') /\ res = INR exc) \/
  ?v es1 rr. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    Inv es1 /\ eval_exprs cx args es1 = (rr, es') /\
    res = (case rr of INL vs => INL (v::vs) | INR exc => INR exc)
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem typed_args_head_admissible[local]:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  cheat
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
  cheat
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
  cheat
QED


Theorem num_of_bytes_l2n:
  !bs. num_of_bytes bs = l2n 256 (MAP w2n bs)
Proof
  cheat
QED

Theorem num_of_be_bytes_word32:
  LENGTH bs = 32 ==>
  num_of_be_bytes bs = w2n (word_of_bytes_be bs : bytes32)
Proof
  cheat
QED

(* A serialized word can be decoded independently of the remaining words.
   Repeated use covers either three- or four-word precompile inputs. *)
Theorem take_pad_word_prefix:
  take_pad_0 32 (word_to_bytes (w:bytes32) T ++ bs) =
    word_to_bytes w T
Proof
  cheat
QED

Theorem drop_word_prefix:
  DROP (32 + n) (word_to_bytes (w:bytes32) T ++ bs) = DROP n bs
Proof
  cheat
QED

Theorem precompile_result_four_words[local]:
  !(h:bytes32) (v:bytes32) (r:bytes32) (s:bytes32).
  precompile_result 1w
    (word_to_bytes h T ++ word_to_bytes v T ++
     word_to_bytes r T ++ word_to_bytes s T) =
  SOME (SOME (case vfmExecution$ecrecover h (w2n v) (w2n r) (w2n s) of
    NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  cheat
QED

Theorem ecrecover_arg_typed_encoding[local]:
  ((?k. tv = BaseTV (UintT k) /\ k <= 256) \/
   tv = BaseTV (BytesT (Fixed 32))) /\ value_has_type tv x ==>
  ecrecover_arg_to_num x = SOME (w2n (typed_val_to_w256 tv x))
Proof
  cheat
QED

Theorem ecrecover_output_encoding[local]:
  ((data = [] /\ (addr:address) = 0w) \/
   data = PAD_LEFT 0w 32 (word_to_bytes addr T)) ==>
  (word_of_bytes_be (TAKE 32 (data ++ REPLICATE 32 0w)) : bytes32) =
  typed_val_to_w256 (BaseTV AddressT) (AddressV addr)
Proof
  cheat
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
  cheat
QED

Theorem ecrecover_run_frag[local]:
  compile_ecrecover h v r sig sa = (op,sb) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb P Q R
Proof
  cheat
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
  cheat
QED

(* Appending a word by MSTORE does not disturb the serialized prefix. *)
Theorem mem_bytes_at_store_append:
  mem_bytes_at a n s.vs_memory = bs ==>
  mem_bytes_at a (n + 32) (mstore (a+n) w s).vs_memory =
    bs ++ word_to_bytes w T
Proof
  cheat
QED

(* Shared three-word prefix: ECMul uses exactly this input layout, while
   ECAdd and ecrecover append a fourth word. *)
Theorem scratch_three_word_stores:
  mem_bytes_at a 96
    (mstore (a+64) r (mstore (a+32) v (mstore a h s))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++ word_to_bytes r T
Proof
  cheat
QED

Theorem scratch_four_word_stores:
  mem_bytes_at a 128
    (mstore (a+96) sig
      (mstore (a+64) r (mstore (a+32) v (mstore a h s)))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++
    word_to_bytes r T ++ word_to_bytes sig T
Proof
  cheat
QED

(* Frozen baseline instance of the shared four-word serialization. *)
Theorem ecrecover_input_stores[local]:
  mem_bytes_at a 128
    (mstore (a+96) sig
      (mstore (a+64) r (mstore (a+32) v (mstore a h s)))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++
    word_to_bytes r T ++ word_to_bytes sig T
Proof
  cheat
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
  cheat
QED

Theorem ecrecover_lookup_generated_update[local]:
  not_fresh_at sa x /\ sa.cs_next_var <= k ==>
  lookup_var x (update_var (STRING #"%" (toString k)) z t) = lookup_var x t
Proof
  cheat
QED

Theorem ecrecover_operand_generated_update[local]:
  (!x. q = Var x ==> not_fresh_at sa x) /\ sa.cs_next_var <= k ==>
  eval_operand q (update_var (STRING #"%" (toString k)) z t) = eval_operand q t
Proof
  cheat
QED

Theorem ecrecover_operand_mstore[local]:
  eval_operand q (mstore a z t) = eval_operand q t
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem state_allocations_disjoint:
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas a = SOME (p,n) /\
  FLOOKUP t.vs_allocas b = SOME (q,m) /\ a <> b ==>
  regions_disjoint p n q m
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem ecrecover_output_write[local]:
  mem_word_at off s.vs_memory = 0w /\
  ((data = [] /\ (addr:address) = 0w) \/
    data = PAD_LEFT 0w 32 (word_to_bytes addr T)) ==>
  mem_word_at off
    (write_memory_with_expansion off (TAKE 32 data) s).vs_memory =
    typed_val_to_w256 (BaseTV AddressT) (AddressV addr)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem computed_suffix_staticcall_dispatch[local]:
  eval_operand gp s = SOME gas /\ eval_operand ap s = SOME addr /\
  eval_operand ip s = SOME ai /\ eval_operand np s = SOME an /\
  eval_operand op s = SOME ro /\ eval_operand zp s = SOME rs ==>
  step_inst_base (mk_inst id STATICCALL [gp; ap; ip; np; op; zp] outs) s =
  exec_ext_call (mk_inst id STATICCALL [gp; ap; ip; np; op; zp] outs)
    s gas addr 0w ai an ro rs T
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem expr_body_pre_stack_result:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  cheat
QED

Theorem expr_sim_pre_stack_result:
  expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> ?tv.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  cheat
QED

Theorem typed_args_ready_of_ok[local]:
  !args ctx func cenv cx env arg_ty.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
           expr_sim_pre cenv cx env e s) /\
    EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args ==>
    typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  cheat
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
  cheat
QED

Theorem typed_stack_args_shape:
  !args cenv cx env arg_ty es.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
           expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es ==>
    wb_args_shape cenv arg_ty args
Proof
  cheat
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
  cheat
QED

Theorem stack_args_values_typed_body:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  cheat
QED

Theorem stack_args_values_typed:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_sim_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  cheat
QED

Theorem typed_builtin_stack_args_values:
  expr_sim_pre cenv cx env (Builtin ann bt args) es /\
  EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args /\
  eval_exprs cx args es = (INL vs,es') ==>
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) args vs
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem lower_value_ecrecover[local]:
  lower_value compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa = (op,sb) ==>
  ?h v r sig sm. lower_word_args cenv (\e. ty) [a;b;c;d] sa = ([h;v;r;sig],sm) /\
    compile_ecrecover h v r sig sm = (op,sb)
Proof
  cheat
QED

Theorem lower_value_ecrecover_args[local]:
  LENGTH args = 4 /\
  lower_value compile_expr cenv ty (Builtin ann ECRecover args) sa = (op,sb) ==>
  ?h v r sig sm. lower_word_args cenv (\e. ty) args sa = ([h;v;r;sig],sm) /\
    compile_ecrecover h v r sig sm = (op,sb)
Proof
  cheat
QED

Theorem compile_ecrecover_stack[local]:
  LENGTH args = 4 /\
  compile_expr cenv ty (Builtin ann ECRecover args) sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  cheat
QED

Theorem compile_ecrecover_extends[local]:
  compile_ecrecover h v r sig sa = (op,sb) ==>
  cs_extends sa sb
Proof
  cheat
QED

Theorem ecrecover_pre_types[local]:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es ==>
  ann = BaseT AddressT /\ LENGTH args = 4 /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem eval_expr_ecrecover_read_action[local]:
  LENGTH args = 4 ==>
  bind (eval_expr cx (Builtin ann ECRecover args)) (read_result cx) =
  bind (eval_exprs cx args)
    (\vs ee. case builtin_result cx ee.accounts ann ECRecover (MAP expr_type args) vs of
       INR exc => (INR exc, ee)
     | INL w => (do precompile_call_success ECRecover; return w od) ee)
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem ecrecover_expr_sim[local]:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es /\
  (!arg_ty. typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
  expr_sim ctx func cenv cx ty (Builtin ann ECRecover args) es
Proof
  cheat
QED

Theorem compile_ecrecover_call_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECRecover args)
Proof
  cheat
QED

