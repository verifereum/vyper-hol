(*
 * Expression simulation: ecadd, ecmul (#636, Builtins row 8)
 *
 * ecadd(a, b) compiles both point operands (compile_expr, unwrap_value),
 * ecmul(a, k) the point and then the scalar (lower_value); only then does
 * compile_ecadd_points / compile_ecmul_point (builtinMisc) ALLOCA the
 * precompile input, load each point word from the operand pointers and
 * store it into the input, ALLOCA a 64-byte output, STATICCALL precompile 6
 * or 7, ASSERT its success word and return the output pointer.
 *
 * The first point's bytes must survive the second operand's fragment and
 * the stores into the input.  The point sits in one of the first
 * fragment's allocations (expr_post_operand_kept_stable) or in a live
 * local (expr_post_operand_local_kept, by expr_post's locals_kept);
 * expr_val_at keeps those two cases apart, and the input, a fresh
 * ALLOCA, is clear of both.  take_outcome answers the call with precompile_result
 * (extCallOracle), which runs verifereum's ecadd/ecmul on the decoded
 * words, as evaluate_ecadd/evaluate_ecmul do: an invalid point fails the
 * call, so the ASSERT reverts where the source raises.  The ALLOCA, the
 * call and the ASSERT are exprSimPrecompiles' shared pieces, also used by
 * ecrecover.
 *
 * TOP-LEVEL:
 *   compile_ecadd_call_case, compile_ecmul_call_case — shared case judgments
 *   for ECAdd and ECMul, including operands with internal calls.
 *
 * Helpers: lower_value_name_safe_operand and generic no-Label support in
 *   exprSafeOperand; ec_point_memory_words, ec_point_operand_kept;
 *   ec_point_word_transfer_run, ec_point_pair_transfer_run,
 *   ec_point_prefix_then_run share point-word movement;
 *   ec_scratch_stores_memory, ec_scratch_stores_capacity and
 *   ec_scratch_stores_frame preserve disjoint regions and immutable bytes;
 *   ec_points_run,
 *   ec_outcome_then composes a value step with a counted continuation;
 *   ec_binary_call_gas composes exprs_case operands under expr_body_pre as
 *   counted gas outcomes;
 *   ec_points_path and compile_ec_call_case share the EC pipeline atop
 *   exprSimPrecompiles' allocated_payload_run and computed-call suffix.
 *)
Theory exprSimECArith
Ancestors
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprOperandVar exprSafeOperand exprSafeOperandBuiltins
  fragExec exprSimHash exprSimWordBuiltins
  exprLowering exprSimHyps exprSimPrecompiles exprSimOperands
  exprSimAttributeFields
  exprSimLiteralBuffer
  exprSimCalldataSlice entryDecodeStaticProps
  builtinMisc venomInst exprLoweringProps venomExecSemantics
  venomState vyperTypeSystem vyperContext valueEncoding
  vyperTyping valueEncodingProofs vyperTypeBuiltins vyperValueOperation
  vyperValue vyperAssignPreservesType compileEnv extCallOracle byte
  vfmBuffer venomMemDefs vfmTypes vfmExecution bn254 list rich_list
  numposrep gasOutcome gasSummary gasSummaryCompose gasExemptCert
  fragGasPath fragGasMode cv_std[ignore_grammar]

Theorem lower_value_name_safe_operand[local]:
  expr_body_pre cenv cx env (Name ann id) es /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv ann (Name ann id) sa = (op,sb) ==>
  safe_operand sb op
Proof
  cheat
QED

Theorem ec_point_builtin_cases[local]:
  well_typed_builtin_app (ArrayT (BaseT (UintT 256)) (Fixed 2)) bi ts ==>
  bi = ECAdd \/ bi = ECMul \/
  bi = MakeArray (SOME (BaseT (UintT 256))) (Fixed 2)
Proof
  cheat
QED


Theorem ec_point_builtin_not_label[local]:
  well_typed_expr env (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bi args) /\
  compile_builtin_dispatch_body cfn cenv
    (ArrayT (BaseT (UintT 256)) (Fixed 2)) ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  cheat
QED
Theorem ec_point_type_builtin_cases[local]:
  type_builtin_result_ok tenv tb (ArrayT (BaseT (UintT 256)) (Fixed 2)) target ts /\
  well_typed_type_builtin_args tb target ts ==>
  tb = Empty \/ ?ensure. tb = AbiDecode ensure
Proof
  cheat
QED

Theorem ec_point_type_builtin_not_label[local]:
  well_typed_expr env
    (TypeBuiltin (ArrayT (BaseT (UintT 256)) (Fixed 2)) tb target args) /\
  compile_type_builtin_dispatch_body cfn cenv
    (ArrayT (BaseT (UintT 256)) (Fixed 2)) ty tb target args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  cheat
QED

Theorem ec_point_call_not_label[local]:
  well_typed_expr env
    (Call (ArrayT (BaseT (UintT 256)) (Fixed 2)) target args drv) /\
  compile_call cfn cenv (ArrayT (BaseT (UintT 256)) (Fixed 2))
    ty target args drv sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  cheat
QED

Theorem ec_point_lower_value_safe_operand[local]:
  expr_body_pre cenv cx env e es /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv (ArrayT (BaseT (UintT 256)) (Fixed 2)) e sa = (op,sb) ==>
  safe_operand sb op
Proof
  cheat
QED


Theorem ecadd_types[local]:
  well_typed_builtin_app ty ECAdd ts ==>
  ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ts = [ArrayT (BaseT (UintT 256)) (Fixed 2);
        ArrayT (BaseT (UintT 256)) (Fixed 2)]
Proof
  cheat
QED

Theorem ecmul_types[local]:
  well_typed_builtin_app ty ECMul ts ==>
  ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ts = [ArrayT (BaseT (UintT 256)) (Fixed 2); BaseT (UintT 256)]
Proof
  cheat
QED

Theorem ec_point_footprint[local]:
  val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64
Proof
  cheat
QED

Theorem ec_uint256_encoding[local]:
  value_has_type (BaseTV (UintT 256)) v ==>
  ?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** 256 /\
      typed_val_to_w256 (BaseTV (UintT 256)) v = n2w (Num i)
Proof
  cheat
QED

Theorem ec_point_index_memory[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (ArrayV av) /\
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
    (ArrayV av) off mem /\ j < 2 ==>
  ?i. array_index (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) av (&j) =
        SOME (IntV i) /\
      0 <= i /\ Num i < 2 ** 256 /\
      mem_word_at (off + j * 32) mem = n2w (Num i)
Proof
  cheat
QED
Theorem ec_point_memory_words[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v op s ==>
  ?w x y. eval_operand op s = SOME w /\
    extract_ec_point v = SOME (x,y) /\
    0 <= x /\ Num x < 2 ** 256 /\ 0 <= y /\ Num y < 2 ** 256 /\
    mem_word_at (w2n w) s.vs_memory = n2w (Num x) /\
    mem_word_at (w2n w + 32) s.vs_memory = n2w (Num y)
Proof
  cheat
QED

Theorem ec_point_operand_kept[local]:
  post_value_type cenv e1 = expr_type e1 /\
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) /\
  local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  s1.cs_next_id <= s2.cs_next_id ==>
  expr_val_rel cx (expr_type e1) v1 x u /\
  expr_val_at cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  cheat
QED

Theorem ec_precompile_words[local]:
  (!x1 y1 x2 y2.
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2)))) /\
  (!x y n.
  precompile_result 7w
    (word_to_bytes (x:bytes32) T ++ word_to_bytes (y:bytes32) T ++
     word_to_bytes (n:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecmul (w2n x,w2n y) (w2n n))))
Proof
  cheat
QED

(* These bounds adapters use distinct affine results: addAffine_bounded
   directly, versus mulAffine_bounded with the valid input point unpacked. *)
Theorem ecadd_success_bounds:
  vfmExecution$ecadd a b = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  cheat
QED

Theorem ecmul_success_bounds:
  vfmExecution$ecmul a n = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  cheat
QED

Theorem ec_result_memory[local]:
  mem_word_at off mem = n2w x /\ mem_word_at (off + 32) mem = n2w y ==>
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
    (mk_ec_result (x,y)) off mem
Proof
  cheat
QED

Theorem ec_precompile_success[local]:
  (!x1 y1 x2 y2 x y.
  vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2) = SOME (x,y) ==>
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))) /\
  (!px py scalar x y.
  vfmExecution$ecmul (w2n px,w2n py) (w2n scalar) = SOME (x,y) ==>
  precompile_result 7w
    (word_to_bytes (px:bytes32) T ++ word_to_bytes (py:bytes32) T ++
     word_to_bytes (scalar:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)))
Proof
  cheat
QED

Theorem ec_points_code_shape[local]:
  (!p1 p2 sa op sb.
  compile_ecadd_points p1 p2 sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)) /\
  (!p scalar sa op sb.
  compile_ecmul_point p scalar sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb))
Proof
  cheat
QED

(* Each interleaved scratch write keeps both words of every disjoint point.
   The two point operands themselves need not be disjoint. *)
Theorem ec_point_words_scratch_store[local]:
  !base sz point off w s.
  regions_disjoint base sz point 64 /\ off + 32 <= sz ==>
  mem_word_at point (mstore (base + off) w s).vs_memory =
    mem_word_at point s.vs_memory /\
  mem_word_at (point + 32) (mstore (base + off) w s).vs_memory =
    mem_word_at (point + 32) s.vs_memory
Proof
  cheat
QED

(* A single point word is loaded before its scratch store, in the exact
   four-instruction order emitted by both EC lowering helpers. *)
Theorem ec_point_word_transfer_run[local]:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value]
   od) sa = ((),sb) /\
  eval_operand point_op s = SOME point /\
  eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword + boff))
        (mem_word_at (w2n (point + poff)) s.vs_memory) s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem ec_point_word_transfer_shape[local]:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value]
   od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_next_id = sa.cs_next_id + 4
Proof
  cheat
QED

Theorem ec_point_transfers_run[local]:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  regions_disjoint (w2n (bword+boff)) 64 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword+boff)+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n (bword+boff)) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* Scratch separation consumes the allocation/local placement disjunction,
   rather than assuming that every point came from a fresh allocation. *)
Theorem ec_point_scratch_disjoint[local]:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sb es v pop s /\
  eval_operand pop s = SOME w /\
  (!aid b sz. aid < sb.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint scratch scratch_size b sz) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint scratch scratch_size b sz) ==>
  regions_disjoint scratch scratch_size (w2n w) 64
Proof
  cheat
QED

Theorem ec_result_val_wf[local]:
  val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y))
Proof
  cheat
QED

Theorem ec_result_pointer_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  stmt_state_rel ctx func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
  eval_operand pop t = SOME w /\
  mem_bytes_at (w2n w) 64 t.vs_memory =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,64) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b sz. local_region cenv es'.scopes t name b sz ==>
     regions_disjoint (w2n w) 64 b sz) ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (mk_ec_result (x,y)))
    (FST (as_ptr_val (expr_type e) LocMemory (pop,sb))) t
Proof
  cheat
QED

Theorem ec_point_fresh_scratch_disjoint[local]:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sa es v pop s /\
  eval_operand pop s = SOME w /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint scratch len b sz) /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
     regions_disjoint scratch len b sz) ==>
  regions_disjoint scratch len (w2n w) 64
Proof
  cheat
QED

Theorem ec_input_stores_shape[local]:
  (!p1 p2 ib sa sb. (do xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y2] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 12 /\
  sb.cs_next_id = sa.cs_next_id + 16) /\
  (!p ib scalar sa sb. (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 7 /\
  sb.cs_next_id = sa.cs_next_id + 10)
Proof
  cheat
QED

Theorem ec_point_pair_transfer_run[local]:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value];
      src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sa = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  regions_disjoint (w2n (bword+boff)) 64 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword+boff)+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n (bword+boff)) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* First-point prefix shared by both payloads.  The tail's operands are
   preserved even when they are labels, since the prefix preserves labels. *)
Theorem ec_point_prefix_then_run[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y]; tail od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) (p::ib::ops) ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n bw + len < dimword (:256) /\ 64 <= len /\
  regions_disjoint (w2n bw) len (w2n point) 64 ==>
  ?sc t.
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib; Lit 32w];
        emit_void MSTORE [dst1; y] od) sa = ((),sc) /\
    tail sc = ((),sb) /\
    run_inst_seq (emitted_insts sa sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sc.cs_next_var = sa.cs_next_var + 6 /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    (!op. MEM op (ib::ops) ==> eval_operand op t = eval_operand op s) /\
    (!x. MEM (Var x) (ib::ops) ==> not_fresh_at sc x)
Proof
  cheat
QED

Theorem ecmul_input_stores_run[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+64) wscalar
        (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
          (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem ecadd_input_stores_run[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+96) (mem_word_at (w2n point2+32) s.vs_memory)
        (mstore (w2n bw+64) (mem_word_at (w2n point2) s.vs_memory)
          (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
            (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* Any finite collection of word stores confined to scratch preserves all
   disjoint observations.  Payload clients only supply offsets and words. *)
Theorem ec_scratch_stores_memory[local]:
  !stores s.
  (!off w. MEM (off,w) stores ==> off + 32 <= len) /\
  regions_disjoint a len b sz ==>
  mem_bytes_at b sz
    (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory =
  mem_bytes_at b sz s.vs_memory
Proof
  cheat
QED

Theorem ec_scratch_stores_capacity[local]:
  !stores s. LENGTH s.vs_memory <=
    LENGTH (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory
Proof
  cheat
QED

Theorem ec_scratch_stores_frame[local]:
  t.vs_memory =
    (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory /\
  (!off w. MEM (off,w) stores ==> off + 32 <= len) /\
  stmt_state_rel ctx func cenv cx es s /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint a len b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint a len b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint a len off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t
Proof
  cheat
QED

Theorem ec_input_stores_sim[local]:
  (!p ib scalar sa sb s point bw wscalar func cenv cx es sc.
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 96 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 96 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes wscalar T) /\
  (!p q ib sa sb s point point2 bw func cenv cx es sc.
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 128 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 128 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T)
Proof
  cheat
QED



Theorem comp_return_bind[local]:
  !x f. comp_bind (comp_return x) f = f x
Proof
  cheat
QED

(* Direct compiler boundary. The legacy buffer-prefix interface below is
   retained only until the allocation-runtime consumers are migrated. *)
Theorem ec_points_prefix[local]:
  (!p scalar sf res sb cenv func.
  compile_ecmul_point p scalar sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sp sm.
    context$compile_alloc_buffer 96 sf = (ib,sa) /\
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; scalar] od) sa = ((),sp) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
      emitted_insts sp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
    sp.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
    sp.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)) /\
  (!p1 p2 sf res sb cenv func.
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sp sm.
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do xp <- emit_op ADD [p1; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p1; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        xp2 <- emit_op ADD [p2; Lit 0w];
        x2 <- emit_op MLOAD [xp2];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; x2];
        yp2 <- emit_op ADD [p2; Lit 32w];
        y2 <- emit_op MLOAD [yp2];
        dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [dst3; y2] od) sa = ((),sp) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 6w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
      emitted_insts sp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
    sp.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
    sp.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x))
Proof
  cheat
QED

Definition ec_source_tail_def:
  ec_source_tail cx ann bt tys vs es =
    case exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs of
      INR ex => (INR ex,es)
    | INL v => (do precompile_call_success bt;
                   vyperState$return (Value v) od) es
End

Theorem ec_source_outcome_step[local]:
  (bt = ECAdd \/ bt = ECMul) ==>
  precompile_call_success bt es =
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

Theorem eval_expr_ec_cases[local]:
  (bt = ECAdd \/ bt = ECMul) /\ LENGTH args = 2 /\
  eval_expr cx (Builtin ann bt args) es = (res,es') ==>
  (?exc. eval_exprs cx args es = (INR exc,es') /\ res = INR exc) \/
  ?vs es1. eval_exprs cx args es = (INL vs,es1) /\
    ec_source_tail cx ann bt (MAP expr_type args) vs es1 = (res,es')
Proof
  cheat
QED

Theorem ec_source_tail_cases[local]:
  (bt = ECAdd \/ bt = ECMul) ==>
  ec_source_tail cx ann bt tys vs es =
    case exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs of
      INR ex => (INR ex,es)
    | INL v =>
        case es.outcomes of
          NONE => (INL (Value v),es)
        | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
        | SOME (co::rest) =>
            (if call_outcome_success co then INL (Value v)
             else INR (Error (RuntimeError "precompile failed")),
             es with outcomes := SOME rest)
Proof
  cheat
QED

Theorem ec_two_args_source[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  eval_expr cx (Builtin ann bt [a;b]) es = (res,es') /\
  (do r <- eval_expr cx a; read_result cx r od) es = (r1,es1) /\
  (do r <- eval_expr cx b; read_result cx r od) es1 = (r2,es2) ==>
  (!ex. r1 = INR ex ==> res = INR ex) /\
  (!v ex. r1 = INL v /\ r2 = INR ex ==> res = INR ex) /\
  (!v1 v2. r1 = INL v1 /\ r2 = INL v2 ==>
    ec_source_tail cx ann bt [expr_type a;expr_type b] [v1;v2] es2 = (res,es'))
Proof
  cheat
QED

Theorem ec_suffix_failure[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  cheat
QED

Theorem ec_suffix_oracle_failure[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  (target = 6w \/ target = 7w) /\
  (s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  cheat
QED

Theorem ec_suffix_pointer_post[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip st = SOME wi /\ eval_operand op st = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  precompile_result (venom_call_request st target 0w wi insz T).cr_target
    (venom_call_request st target 0w wi insz T).cr_data =
    SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)) /\
  st.vs_outcomes = co::rest /\ co.co_success /\
  stmt_state_rel ctx func cenv cx es st /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sf /\
  wb_frame cenv es sf s0 st /\ w2n wo + 64 < dimword (:256) /\
  FLOOKUP st.vs_allocas aid = SOME (w2n wo,64) /\
  sf.cs_next_id <= aid /\ aid < sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes st name b sz ==>
     regions_disjoint (w2n wo) 64 b sz) /\
  (!old b sz. old < sf.cs_next_id /\ FLOOKUP st.vs_allocas old = SOME (b,sz) ==>
     regions_disjoint (w2n wo) 64 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  ?t. run_inst_seq (emitted_insts sm sb) st = OK t /\
      vv_post ctx func cenv cx e es sf sb s0 (es with outcomes := SOME rest)
        (Value (mk_ec_result (x,y)))
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
Proof
  cheat
QED

Theorem ec_points_run[local]:
  (!p scalar sf res sb func cenv cx es s point wscalar lo v e.
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME wscalar /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sf z) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  w2n point + 64 < dimword (:256) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  case vfmExecution$ecmul
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n wscalar) of
    NONE => ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t
  | SOME (x,y) =>
      if (?co rest. s.vs_outcomes = co::rest /\ co.co_success) then
        ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
          vv_post ctx func cenv cx e es sf sb s
            (es with outcomes := SOME (DROP 1 s.vs_outcomes))
            (Value (mk_ec_result (x,y)))
            (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
      else ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t) /\
  (!p1 p2 sf res sb func cenv cx es s point point2 lo v1 v2 e.
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
  (!z. MEM (Var z) [p1;p2] ==> not_fresh_at sf z) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  w2n point + 64 < dimword (:256) /\ w2n point2 + 64 < dimword (:256) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  case vfmExecution$ecadd
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory))
    (w2n (mem_word_at (w2n point2) s.vs_memory),
     w2n (mem_word_at (w2n point2+32) s.vs_memory)) of
    NONE => ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t
  | SOME (x,y) =>
      if (?co rest. s.vs_outcomes = co::rest /\ co.co_success) then
        ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
          vv_post ctx func cenv cx e es sf sb s
            (es with outcomes := SOME (DROP 1 s.vs_outcomes))
            (Value (mk_ec_result (x,y)))
            (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
      else ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t)
Proof
  cheat
QED





Theorem ec_pre_types[local]:
  (!cenv cx env ann args es.
  expr_body_pre cenv cx env (Builtin ann ECAdd args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = ArrayT (BaseT (UintT 256)) (Fixed 2)) /\
  (!cenv cx env ann args es.
  expr_body_pre cenv cx env (Builtin ann ECMul args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = BaseT (UintT 256))
Proof
  cheat
QED

Theorem compile_ec_operands[local]:
  (!cenv ty ann a b sa vv sb.
  compile_expr cenv ty (Builtin ann ECMul [a;b]) sa = (vv,sb) ==>
  ?p scalar s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (BaseT (UintT 256)) b s1 = (scalar,sm) /\
    compile_ecmul_point p scalar sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb))) /\
  (!cenv ty ann a b sa vv sb.
  compile_expr cenv ty (Builtin ann ECAdd [a;b]) sa = (vv,sb) ==>
  ?p q s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
    compile_ecadd_points p q sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb)))
Proof
  cheat
QED

Theorem ec_point_pointer_bound[local]:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo hi es v p s /\
  eval_operand p s = SOME w ==>
  w2n w + 64 < dimword (:256)
Proof
  cheat
QED

Theorem ec_memory_semantics[local]:
  (!v1 v2 cx p1 p2 s.
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (BaseTV (UintT 256)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (BaseT (UintT 256)) v2 p2 s ==>
  ?point sw.
    eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME sw /\
    evaluate_ecmul [v1;v2] =
      (case vfmExecution$ecmul
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n sw) of
         NONE => INR (RuntimeError "ECMul invalid point")
       | SOME r => INL (mk_ec_result r))) /\
  (!v1 v2 cx p1 p2 s.
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 p2 s ==>
  ?point point2.
    eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
    evaluate_ecadd [v1;v2] =
      (case vfmExecution$ecadd
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory))
        (w2n (mem_word_at (w2n point2) s.vs_memory),
         w2n (mem_word_at (w2n point2+32) s.vs_memory)) of
         NONE => INR (RuntimeError "ECAdd invalid point")
       | SOME r => INL (mk_ec_result r)))
Proof
  cheat
QED

Theorem ec_points_path[local]:
  (!p scalar sf res sb func cenv cx es s lo v k e ctx ann tys r es'.
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sf z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  value_has_type (BaseTV (UintT 256)) k /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p s /\
  expr_val_rel cx (BaseT (UintT 256)) k scalar s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ec_source_tail cx ann ECMul tys [v;k] es = (r,es') /\
  fn_has_code sf sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?n r'. gas_marked_path F ctx func s n r' /\
    ((?w. r' = OK w /\
        (?a. r = INL a /\
           vv_post ctx func cenv cx e es sf sb s es' a
             (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) w) /\
        w.vs_current_bb = sb.cs_current_bb /\
        w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r' /\ expr_exit r r'))) /\
  (!p1 p2 sf res sb func cenv cx es s lo v1 v2 e ctx ann tys r es'.
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  (!z. MEM (Var z) [p1;p2] ==> not_fresh_at sf z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 p2 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ec_source_tail cx ann ECAdd tys [v1;v2] es = (r,es') /\
  fn_has_code sf sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?n r'. gas_marked_path F ctx func s n r' /\
    ((?w. r' = OK w /\
        (?a. r = INL a /\
           vv_post ctx func cenv cx e es sf sb s es' a
             (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) w) /\
        w.vs_current_bb = sb.cs_current_bb /\
        w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r' /\ expr_exit r r')))
Proof
  cheat
QED



Theorem ec_expr_exit_INR_cast[local]:
  expr_exit (INR exc : value + exception) r ==>
  expr_exit (INR exc : eval_result + exception) r
Proof
  cheat
QED

(* A value step followed by a continuation whose outcome is counted from
   every normal endpoint of the step. *)
Theorem ec_outcome_then[local]:
  gas_outcome F tops (ctx,func)
    (m : evaluation_state -> value evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t) (\res ee r. expr_exit res r) /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==>
     R (INR exc) ee r) /\
  (!gs v ee t. m (es with gas_obs := gs) = (INL v, ee) /\ ee.gas_obs = [] /\
     P v ee t /\ ~t.vs_halted ==>
     gas_outcome F tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome F tops (ctx,func) (bind m k) (es,s0) Q R
Proof
  cheat
QED

Theorem ec_eval_bind[local]:
  (bt = ECAdd \/ bt = ECMul) ==>
  eval_expr cx (Builtin ann bt [a;b]) =
  bind (bind (eval_expr cx a) (read_result cx))
    (\v1. bind (bind (eval_expr cx b) (read_result cx))
      (\v2. ec_source_tail cx ann bt [expr_type a; expr_type b] [v1;v2]))
Proof
  cheat
QED

Theorem ec_source_tail_gas_obs[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  ec_source_tail cx ann bt tys vs es = (r,es') ==>
  ec_source_tail cx ann bt tys vs (es with gas_obs := g) =
    (r, es' with gas_obs := g)
Proof
  cheat
QED

Theorem ec_source_tail_scopes[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  ec_source_tail cx ann bt tys vs es = (r,es') ==>
  es'.scopes = es.scopes
Proof
  cheat
QED

(* Both operands as counted outcomes, then the point suffix as an actual
   counted target path from every pair of operand endpoints. *)
Theorem ec_binary_call_gas[local]:
  exprs_case nocalls ctx func cenv cx [a;b] /\
  expr_body_pre cenv cx env (Builtin ann bt [a;b]) es /\
  (nocalls ==> int_calls_expr (Builtin ann bt [a;b]) = []) /\
  (bt = ECAdd \/ bt = ECMul) /\
  expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  cs_extends sm sb /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!es1 es2 v1 v2 t u res es'.
    expr_post ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
    expr_post ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
    expr_val_rel cx (expr_type a) v1 p u /\
    expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u /\
    expr_result_typed env a (Value v1) /\ expr_result_typed env b (Value v2) /\
    stmt_state_rel ctx func cenv cx es2 u /\ local_ptrs_reserved cenv sm /\
    fn_has_code sm sb func /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!z. MEM (Var z) [p;q] ==> not_fresh_at sm z) /\
    ec_source_tail cx ann bt [expr_type a;expr_type b] [v1;v2] es2 = (res,es') ==>
    ?n r. gas_marked_path F ctx func u n r /\
      ((?w. r = OK w /\
          (?tv. res = INL tv /\
             vv_post ctx func cenv cx (Builtin ann bt [a;b]) es2 sm sb u es'
               tv vv w) /\
          w.vs_current_bb = sb.cs_current_bb /\
          w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\ expr_exit res r))) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (Builtin ann bt [a;b]))
    (es,s0)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx (Builtin ann bt [a;b]) es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  cheat
QED

Theorem compile_ec_call_case[local]:
  (!nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECMul args)) /\
  (!nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECAdd args))
Proof
  cheat
QED



Theorem compile_ecadd_call_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECAdd args)
Proof
  cheat
QED

Theorem compile_ecmul_call_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECMul args)
Proof
  cheat
QED
