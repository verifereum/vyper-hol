Theory abiArgsObserverProbe
Ancestors
  exprLowering compileEnv context vyperAST fragExec venomWf
  venomInst finite_map

Definition observer_probe_start_def:
  observer_probe_start = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "@exit_2"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition observer_probe_end_def:
  observer_probe_end ce = SND (lower_value compile_expr ce (BaseT BoolT)
    (IfExp (BaseT BoolT) (Literal (BaseT BoolT) (BoolL T))
      (Literal (BaseT BoolT) (BoolL T)) (Literal (BaseT BoolT) (BoolL F)))
    observer_probe_start)
End

Theorem observer_probe_collision:
  let ce = ce with ce_vars := FEMPTY in
  let sb = observer_probe_end ce in
  sb.cs_current_insts = [] /\
  (?bb. MEM bb (emitted_blocks observer_probe_start sb) /\
        bb.bb_label = sb.cs_current_bb) /\
  fn_has_code observer_probe_start sb
    (fn with fn_blocks := sb.cs_blocks) /\
  fn_inst_ids_distinct (fn with fn_blocks := sb.cs_blocks)
Proof
  EVAL_TAC >> rpt conj_tac
  >- (qexists_tac `LAST (observer_probe_end (ce with ce_vars := FEMPTY)).cs_blocks` >> EVAL_TAC)
  >- (rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> BETA_TAC >> simp[]
QED

(* The direct uncaptured Label image has no emitted code, even with hostile
   initial labels. This tests only Name, not all forwarding constructors. *)
Theorem observer_probe_name_label:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz) /\
  ~is_word_type (expr_type (Name ann id)) ==>
  lower_value compile_expr ce ty (Name ann id) sa = (Label l,sa) /\
  (!bb. MEM bb (emitted_blocks sa sa) ==> bb.bb_label <> sa.cs_current_bb)
Proof
  simp[lower_value_def, comp_bind_def, Once compile_expr_def,
       compile_expr_body_def, compile_name_vv_def, unwrap_value_def,
       mk_ptr_def, comp_return_def, emitted_blocks_def]
QED

(* A Label result need not leave the complete compiler state unchanged:
   narrowing a dynamic bytestring inserts a run-time length assertion. *)
Theorem observer_probe_label_conversion_effect:
  let ce = ce with ce_vars := FEMPTY |++ [("x", PtrVar (Label l) 288)] in
  let e = TypeBuiltin (BaseT (BytesT (Dynamic 4))) Convert
    (BaseT (BytesT (Dynamic 4))) [Name (BaseT (BytesT (Dynamic 8))) "x"] in
  let (op,sb) = lower_value compile_expr ce (expr_type e) e observer_probe_start in
    op = Label l /\ sb.cs_blocks = observer_probe_start.cs_blocks /\
    sb <> observer_probe_start
Proof
  EVAL_TAC >> simp[]
QED

(* C1.3.7.4.11 compiler-image audit (not a universal theorem).

   Classification: N = result cannot be Label, F = input forwarding.
   All claims below are source classifications; only the named probe theorems
   above are kernel-checked compiler-image facts. No typing/state/environment
   coherence is used. A fresh operand is Var regardless of hostile supplies.

   Backward boundary:
   unwrap_value: StackValue forwards unchanged; LocatedValue word loads via
   compile_ptr_load (all five locations produce Var, including ctor/code);
   nonword LocMemory forwards unchanged; all other locations allocate a fresh
   buffer via compile_ensure_in_memory (context). Thus a Label result implies
   the incoming vv_operand is that Label and unwrapping itself is identity.
   This implication is the intended checked inversion lemma, not yet proved.

   compile_expr_body matrix (exprLowering):
   Literal: N. Word/fallback BytesL yields Lit; StringL (including fallback)
     and dynamic BytesL yield fresh allocation. compile_literal_vv.
   Name: F, only PtrVar (Label l) environment entry; state unchanged.
     MemLoc yields Lit; missing/nonlocal entry emits INVALID and returns Lit.
   IfExp: N, Var result_var, either stack or memory pointer. Its blocks can
     collide with endpoint: observer_probe_collision. Never forwards branches.
   Builtin AddMod/MulMod/PowMod256 name fast paths: N, final arithmetic emit;
     compile_*_names use compile_name_vv/unwrap but do not forward their values.
   Builtin general / TypeBuiltin: dispatcher predicates required below.
   Subscript: N in ALL place_type branches. Tuple and struct ALWAYS emit ADD
     via compile_tuple_subscript, including offset zero/unknown fields/index.
     Mapping emits final SHA3; generic ValPT (including nonarray fallback)
     emits final ADD via compile_array_subscript. Index effects cannot escape
     as a forwarded base. No recursive Label preservation needed in this case.
   Attribute: N, final ADD even absent field/default struct name/zero offset.
   StructLit: N, fresh compile_alloc_buffer result, even empty fields/size zero.
   FlagMember: N, Lit even arbitrary member-id metadata.
   TopLevelName: N, known storage/transient/code slots are Lit; other/missing
     entries emit INVALID then Lit. Unwrapping nonmemory cannot create Label.
   Call: N; full target split below. Pop: N, compile_dynarray_pop final ADD;
     fallback target place/location/element type does not bypass that ADD.

   compile_call matrix:
   IntCall: fresh allocation buffer for positive returns_count or buffer size;
     no buffer => Lit 0; syntactic SOME/NONE positive-return fallback INVOKE
     emits Var. emit_multi_op results are stored, not returned as operands.
   ExtCall []: INVALID/Lit. Nonempty: compile_external_call_kwargs returns
     Lit 0 for void, otherwise fresh result allocation. Default path copies
     default_op into result_op and returns result_op, NOT default_op (lines
     928-960); both default/decode paths may emit blocks but cannot yield Label.
   Send: valid shape CALL/ASSERT then Lit; both invalid shapes INVALID/Lit.
   RawCallTarget/RawCallCalldataTarget: malformed INVALID/Lit; otherwise
     compile_raw_call_finish returns Lit 0, fresh success Var, fresh tuple
     allocation, or out_val from compile_raw_call_outbuf (fresh allocation).
   RawLog, RawRevert, SelfDestructTarget, CreateTarget: INVALID/Lit.

   compile_builtin_dispatch_body complete constructor matrix:
   Bop: N in array-literal membership (empty Lit or EQ/OR/AND), variable array
     membership (fresh result_var or ISZERO), bytes equality (EQ/ISZERO), and
     ordinary compile_binop. compile_binop arithmetic returns emitted result,
     including all safe_pow branches; unsafe wrap forwards only fresh result;
     bitwise/shifts/comparisons/Min/Max/membership emit; catch-all INVALID/Lit.
   Not: N, ISZERO or compile_invert XOR/NOT. Neg: N final SUB.
   Abs: N, compile_select ends with XOR. Env: N, all env cases emit.
   Acc: Balance/Codesize/Codehash/IsContract N (emit); Code N (INVALID/Lit);
     Address F, lower_value of sole child at BaseT AddressT, no extra effects.
   Keccak256/Sha256: N for bytestring/fixed-bytes/word paths (SHA3/MLOAD).
   CalldataLen: N, CALLDATASIZE. CalldataSlice: N, allocated output buffer.
   Len: N, location-aware load. BlockHash/BlobHash: N, final hash opcode.
   AddMod/MulMod/PowMod256: N, arithmetic opcode. Ceil/Floor: N, final SDIV.
   ECRecover: N, MLOAD. ECAdd/ECMul: N, fresh precompile output allocation.
   Concat: N, fresh buf_op_alloc, irrespective of argument effects/empty list.
   Slice: N in msg.data/self.code/extcode/general bytestring/fixed-bytes paths;
     compile_slice_data/code/calldata allocate output; extcode returns out_buf
     supplied by compile_slice_out_buf, never source/start/length operands.
   Uint2Str: N, fresh allocation. AsWeiValue: F ONLY nondecimal scale=1
     (Wei) returns child without effects; decimal path emits Div, other scales
     return fresh MUL result. MethodId: N, literal compilation or runtime
     SHR/SHL/fresh allocation. MakeArray NONE/SOME: N, fresh buffer supplied to
     compile_make_tuple/array; these helpers return that buffer, not a child.
   Partial HD/EL on malformed argument lists does not add return branches:
     guarded callbacks either recurse on a smaller arbitrary chosen expression
     or invalid_expr_call returns Lit 0 after INVALID. N classifications remain
     N; F cases require the callback invariant for every ty/env/state.

   compile_type_builtin_dispatch_body complete constructor matrix:
   Convert: F or N; detailed conversion matrix below. Empty word: Lit 0;
     complex: fresh buffer even size zero. MaxValue/MinValue/Epsilon: Lit.
   Extract32: N, compile_extract32_load fresh MLOAD, then clamps may forward
     only that fresh result. AbiEncode singleton word/nonword and tuple:
     N, lower_abi_encode returns fresh allocated output. AbiDecode: N,
     lower_abi_decode output allocation. No decoder changes proposed.

   compile_type_convert complete forwarding matrix:
   F (input unchanged, possibly checks): ConvIntToInt, ConvToAddress,
     ConvToFlag, ConvBytesMToBytesM, ConvBytestringCast, ConvIdentity.
     All emitted checks in these F paths use emit_op/emit_void only, never
     new_block. compile_int_clamp likewise forwards input with no new blocks.
   N: ConvToBool; ConvBytesToInt; ConvIntToBytesM; ConvIntToDecimal;
     ConvDecimalToInt; ConvBoolToDecimal; ConvBytesToAddress;
     ConvBytesMToDecimal; ConvBytestringToBool/Int/Decimal/BytesM;
     ConvFixedToBytestring. Shifted/clamped values in these paths are already
     fresh; allocation returns fresh. mk_convert_op defaults to ConvIdentity,
     so arbitrary/malformed types do NOT permit claiming absence of Label.
   The checked conversion probe refutes sm=sa even at ty=expr_type e. The
   remaining blocks-only candidate is consistent with the entire matrix,
   but NOT yet proved. In particular no claimed effect-freedom theorem exists.

   Recursion interface inspected by temporary mp_tac compile_expr_ind probe:
   three predicates P0 ce ty e st, P1 ce rt ty bi args st,
   P2 ce vt ty tb rt args st. Expr case IHs cover all child expressions with
   expr_size child < expr_size e and dispatcher lists with list_size expr_size
   args < expr_size e, at arbitrary environments/types/states. Dispatcher IHs
   cover expr_size child < list_size expr_size args. Type dispatcher has an
   additional vacuous F => P1 ... (Env TimeStamp) [] st premise.
   The probe was removed; evidence is the recorded build failure output.

   Proposed bounded proof architecture for strategist review, NOT admissions:
   Define result invariant R sa (vv,sb) :=
     (!l. vv_operand vv = Label l ==> sb.cs_blocks = sa.cs_blocks).
   Instantiate all three induction predicates with R of the actual compiler
   result; arbitrary ty is essential for callbacks (e.g. Acc Address), though
   the eventual consumer uses expr_type e. Guarded callback default is Lit.
   First export unwrap inversion stated above. Then prove each nonforwarding
   helper cannot produce Label, with input buffer non-Label hypotheses for
   forwarding output-buffer helpers. Export type_convert Label inversion:
     compile_type_convert op conv sa = (Label l,sb) ==>
       op = Label l /\ sb.cs_blocks = sa.cs_blocks.
   No global callback monotonicity is needed for N paths: their result
   provenance alone discharges R. Only Acc Address, AsWeiValue scale=1, Convert
   and dispatcher delegation consume recursive Label IHs. For these paths
   preceding actions are solely the child evaluation (no earlier sibling),
   and post-child actions preserve cs_blocks. Compose via unwrap inversion.
   Finally lower_value Label implies equal block lists, hence emitted_blocks
   is empty; observer containment then follows without initial label freshness.
   This is a source-audited argument, not authorization to integrate R before
   its universal theorem and observer applicability have been checked.
*)
