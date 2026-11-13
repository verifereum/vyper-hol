# Fixed RawLog suffix contracts (declaration recovery)

This is specification evidence only, not proof credit. Intended consumers: L0025 (Path) and L0029 (join). No theorem or definition is introduced by this document.

## Provenance and delivery

- FixedCompose owner L0007 published the entire declaration of `raw_log_fixed_data_full_from_endpoints`, source lines 47–191 through `Proof`: persisted output `TO_s4170_rawlog-L0007-20261113T045828762075Z_m0059_t001`. This is the complete unchanged A / revised T / unchanged F source excerpt; its universal A occupies lines 48–76, universal T lines 77–121, universal F lines 122–190. Consume the original output with `read_tool_output` to avoid rendering truncation. Owner checkpoint E0101 records delivery.
- Original donor owner L0006 explicitly confirms `raw_log_fixed_tail_full` is absent from its current own source inventory (E0100). Full 34-line safety-only donor excerpt: `TO_s4170_rawlog-L0006-20261113T045733888689Z_m0117_t001`; inventory/search: `TO_s4170_rawlog-L0006-20261113T045733888689Z_m0115_t001`. No old full-tail declaration is reconstructed here.
- Frame owner L0028 delivered its literal declaration in `TO_s4170_rawlog-L0028-20261113T045843971522Z_m0052_t001` (E0102), copied below. Path proposal and equality check below use that declaration, not a failed proof goal.

## Universal T, verbatim from current conditional consumer

```sml
  (!buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_id <= alloc_sa.cs_next_id /\
    sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
      expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
      expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
      (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2)
```

## Full-tail declaration

The proposed `raw_log_fixed_tail_full` is exactly the universal T above, removing only its outer parentheses and preceding it with `Theorem raw_log_fixed_tail_full:`. No implicit free-variable closure is substituted for its explicit quantifier list. In particular both reservations, the original sa anchor, the serializer equality, and the endpoint quantifiers before H are retained. The complete literal named declaration will be included with the final Frame/Path comparison before checkpoint review.

## Current Frame declaration (verbatim)

Owner excerpt: `TO_s4170_rawlog-L0028-20261113T045843971522Z_m0052_t001`, lines 10–42; dispatch checkpoint E0102. Its proof is not certified by this document.

```sml
Theorem raw_log_fixed_tail_post_frame:
  emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
  compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\
  fn_has_code alloc_sa data_sa func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\
  (!name b n. local_region cenv ee.scopes s name b n ==>
    regions_disjoint (w2n w) 32 b n) /\
  (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
    regions_disjoint (w2n w) 32 b n) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  u = ((mstore (w2n w) word s) with
    <|vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
      vs_inst_idx := LENGTH sb.cs_current_insts|>) ==>
  expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
  expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
  (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
    ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
  stmt_state_rel H ctx func cenv cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) u /\
  storage_well_formed_on cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H)
Proof
```

## Proposed matching Path declaration

This is a proposed interface, not an admission or a proved theorem. It retains T's exact antecedent and explicit universal closure; only its conclusion selects the concrete runtime/ghost endpoint and the Path-owned obligations. No runtime premise is added. The concrete endpoint and ghost updates are selected before H; the equalities are guarded, so no valid-horizon existence is required.

```sml
Theorem raw_log_fixed_tail_path:
  !buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_id <= alloc_sa.cs_next_id /\
    sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      u = ((mstore (w2n w) word s) with
        <|vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
          vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
      (let i = mk_inst sm.cs_next_id MSTORE [buf.buf_operand;data_op] [];
           j = mk_inst s1.cs_next_id LOG
             (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [];
           t = mstore (w2n w) word s;
           t1 = t with vs_inst_idx := SUC s.vs_inst_idx;
           v = t1 with vs_logs := s.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs]
       in G2 = step_prov PG (step_prov PG G i t) j v /\
          tn2 = step_taint j t1 v (step_taint i s t tn)) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
```

## Pointwise join check

For a fixed H satisfying the unchanged guard, every Frame antecedent except its endpoint equation is a literal conjunct of T's static or guarded input (the two `fn_has_code` facts are merely regrouped). The endpoint equation is a literal conjunct of proposed Path's guarded conclusion. Frame then supplies exactly T's `expr_post`, `expr_store_bound`, `alloca_history`, allocation monotonicity, `ptr_val_ok`, and conditional `ptr_buf_ok` at the same u, G2, tn2. Path supplies exactly T's `gas_origin_ptr_path`, cursor equations, `ghost_inv_at`, and `ghost_kept_at` at those witnesses. No independent existential endpoints are conjoined.

Frame additionally concludes state relation and storage well-formedness; they may be used for proving Path ghost preservation pointwise, but must not be moved to unguarded premises. Path may calculate this concrete endpoint itself, then use Frame at that endpoint; the join never asks Frame to choose an endpoint. A and F remain unchanged at the complete persisted source excerpt cited above.

## Literal named full-tail declaration proposed from T

```sml
Theorem raw_log_fixed_tail_full:
  !buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_id <= alloc_sa.cs_next_id /\
    sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
      expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
      expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
      (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
```
