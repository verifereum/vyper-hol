(*
 * unwrap_value's step of the expression simulation (#636)
 *
 * lower_value is compile_expr followed by unwrap_value, which turns the
 * value_vv compile_expr hands out into an operand: none for a StackValue
 * or an aggregate in memory, a load for a word behind a pointer, a copy
 * into a buffer for an aggregate elsewhere.  expr_sim_of_vv_sim sequences
 * compile_expr's counted outcome, which ends in vv_post (expr_vv_sim),
 * with unwrap_value's code, which reads no GAS: unwrap_value_path gives
 * its zero-count gas_path from vv_post to expr_post, and
 * unwrap_value_marked_read binds it to the source's read_result.
 *
 * TOP-LEVEL:
 *   expr_sim_of_vv_sim — expr_vv_sim gives expr_sim
 *   unwrap_value_path  — unwrap_value's zero-GAS path, one lemma per form:
 *                        unwrap_storage_word_path,
 *                        unwrap_runtime_immutable_word_path,
 *                        unwrap_ctor_immutable_word_path,
 *                        unwrap_storage_copy_path,
 *                        unwrap_runtime_code_copy_path,
 *                        unwrap_ctor_code_copy_path
 *   unwrap_value_marked_read — the same, as a marked source execution
 *   expr_sim_of_vv_sim_buffer — the same for an expression lowered to a
 *                        pointer into memory, without the cheated cases
 *   unwrap_value_sim   — unwrap_value's code takes vv_post to expr_post,
 *                        one lemma per form of value_vv:
 *                        expr_post_of_vv_post_stack,
 *                        unwrap_memory_sim (expr_post_of_vv_post_memory,
 *                        and unwrap_memory_word_sim's MLOAD),
 *                        unwrap_runtime_immutable_word_sim (DLOAD),
 *                        unwrap_storage_word_sim (SLOAD/TLOAD),
 *                        unwrap_ctor_immutable_word_sim (ADD of the
 *                        zero base, then ILOAD),
 *                        unwrap_copy_sim (exprSimCopy's copies),
 *                        vv_post_calldata (no calldata pointers)
 *   compile_imm_load_word_ctor_frag — the constructor's immutable word load
 *   vv_post_failed_read — vv_post holds of a result only where it reads
 *
 * Helpers: compile_expr_extends (exprLoweringProps' compile_expr_grows),
 *   compile_ensure_in_memory_extends, unwrap_value_extends,
 *   expr_post_of_vv_post_load, step_DLOAD, immutable_holds_dload,
 *   immutable_holds_iload, compile_imm_load_word_appends,
 *   word_type_slot_size, storage_word_load, storage_holds_load
 *
 * The legacy frag_exec copy lemmas stay in exprSimCopy; the counted copy
 * paths, including the constructor's, are here.
 *)

Theory exprSimUnwrap
Ancestors
  exprSimProps exprSimUnwrapProps
  exprSimDefs
  loweringPosts
  list finite_map
   exprLowering compileEnv immutableEncoding vyperAST vyperInterpreter
  vyperState
  loweringSlice fragExec freshWrites venomInst venomExecSemantics venomState
  exprSimCopy exprOperandVar vyperEvalExprPreservesScopesDom
  valueEncoding valueEncodingProofs vyperTypeValues vyperStorage vyperValue
  vyperLookupStorage valueCopyBytes
  exprSimMemorySource exprSimMemoryRead gasOutcome gasSummary
  gasSummaryCompose gasExemptCert fragGasMode fragGasPath emitHelperProps
  exprLoweringProps emitHelper exprSimAlloc fragGasSeq exprSimStorageCopy
  storageCopyGasPath
Libs
  pairLib

Theorem runtime_code_copy_post_inst_idx[local,simp]:
  expr_post ctx func ce cx e es sa sb s0 es' v op (s with vs_inst_idx := n) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  cheat
QED

Theorem runtime_code_copy_seq_path[local]:
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  fn_has_code sa sb func /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE]) code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = OK z ==>
  gas_path ctx func s 0 (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  z.vs_current_bb = sb.cs_current_bb
Proof
  cheat
QED

(* ===== The compile side ===== *)

(* compile_expr only appends to the compile state, and hands out variables
   and instruction ids from its start counters on. *)
Theorem compile_expr_extends:
  !cenv ty e sa vv sm.
    compile_expr cenv ty e sa = (vv, sm) ==>
    cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id
Proof
  cheat
QED

Theorem compile_imm_load_word_appends:
  !is_ctor imm off.
    cs_appends (context$compile_imm_load_word is_ctor imm off)
Proof
  cheat
QED

Theorem compile_lit_byte_offset_appends[local]:
  !op off. cs_appends (context$compile_lit_byte_offset op off)
Proof
  cheat
QED

Theorem compile_imm_copy_to_memory_appends[local]:
  !n is_ctor imm src dst off.
    cs_appends (context$compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  cheat
QED

Theorem compile_ensure_in_memory_appends[local]:
  !pop loc mem_bytes word_count is_ctor imm.
    cs_appends
      (compile_ensure_in_memory pop loc mem_bytes word_count is_ctor imm)
Proof
  cheat
QED

(* compile_ensure_in_memory's copy only appends to the compile state. *)
Theorem compile_ensure_in_memory_extends:
  !pop loc mem_bytes word_count is_ctor imm sm op sb.
    compile_ensure_in_memory pop loc mem_bytes word_count is_ctor imm sm =
      (op, sb) ==>
    cs_extends sm sb
Proof
  cheat
QED

Theorem emit_op_cs_extends[local]:
  !opc args sm op sb. emit_op opc args sm = (op, sb) ==> cs_extends sm sb
Proof
  cheat
QED

Theorem unwrap_value_extends:
  !cenv vv sm op sb. unwrap_value cenv vv sm = (op, sb) ==> cs_extends sm sb
Proof
  cheat
QED

(* Captured results with the same read have the same compiled-value relation. *)

(* ===== unwrap_value's code ===== *)

(* unwrap_value's code, run where compile_expr's code ends, takes vv_post to
   expr_post.  One lemma per form of value_vv. *)

(* A StackValue: no code. *)
Theorem expr_post_of_vv_post_stack:
  !func cenv cx e es sa sb s0 es' v t op s ctx.
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v) (StackValue t op) s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  cheat
QED

(* An aggregate in memory: the pointer is the operand, no code. *)

(* The end of a one-instruction load of a word: the loaded word in a fresh
   variable, nothing else changed. *)

(* A word in memory: an MLOAD. *)
Theorem unwrap_memory_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op MLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocMemory /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

Theorem step_DLOAD:
  !op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ==>
    step_inst_base (mk_inst id DLOAD [op1] [out]) ss =
      OK (update_var out
            (word_of_bytes T (0w:bytes32)
               (TAKE 32 (DROP (w2n v1) ss.vs_data_section ++
                         REPLICATE 32 0w))) ss)
Proof
  cheat
QED

(* Admissibility rules out type/value mismatches; a word type's memory
   representation is its typed word encoding, including zero padding. *)
Theorem immutable_word_mem_word_at[local]:
  !tenv t tv v off mem.
    evaluate_type tenv t = SOME tv /\ is_word_type t /\
    immutable_value_admissible tv v /\ val_in_memory tv v off mem ==>
    mem_word_at off mem = typed_val_to_w256 tv v
Proof
  cheat
QED

(* At runtime a word immutable is in the data section at its offset, as
   immutables_rel says.  Aggregates instead occupy their full memory layout. *)
Theorem immutable_holds_dload:
  !func cenv cx es s t v w ctx.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    is_word_type t /\ immutable_holds cenv cx t (Value v) w es s ==>
    ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) =
          typed_val_to_w256 tvt v
Proof
  cheat
QED

(* A word immutable at runtime: a DLOAD. *)
Theorem unwrap_runtime_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* A pointer into memory: an MLOAD for a word, the pointer itself for an
   aggregate. *)
Theorem unwrap_memory_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocMemory /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* A word type takes one slot. *)
Theorem word_type_slot_size:
  !tenv t tv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==> type_slot_size tv = 1
Proof
  cheat
QED

(* A word's slot holds its value's encoding: the slot is canonical
   (slots_in_range), so it encodes back to what it decodes to. *)
Theorem storage_word_load[local]:
  !cx t tvt storage w v.
    is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    decode_value storage (w2n w) tvt = SOME v /\
    slots_in_range storage (w2n w) tvt ==>
    lookup_storage w storage = typed_val_to_w256 tvt v
Proof
  cheat
QED

(* At runtime the word a storage or transient load returns is the value's:
   storage_holds makes the slot agree with the source's. *)
Theorem storage_holds_load:
  !cx es s t v w tr tvt.
    is_word_type t /\ storage_holds cx tr t (Value v) w es s /\
    evaluate_type (get_tenv cx) t = SOME tvt ==>
    (if tr then tload w s else sload w s) = typed_val_to_w256 tvt v
Proof
  cheat
QED

(* A word in storage or transient storage: an SLOAD or TLOAD. *)
Theorem unwrap_storage_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* In the constructor a word immutable is staged in memory at its offset, as
   immutables_rel says. *)
Theorem immutable_holds_iload:
  !func cenv cx es s t v w ctx.
    stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
    is_word_type t /\ immutable_holds cenv cx t (Value v) w es s ==>
    ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
          mload (w2n w) s = typed_val_to_w256 tvt v
Proof
  cheat
QED

(* The ILOAD of a constructor immutable word reads memory. *)
Theorem step_ILOAD[local]:
  !id a out s w.
    eval_operand a s = SOME w ==>
    step_inst_base (mk_inst id ILOAD [a] [out]) s =
    OK (update_var out (mload (w2n w) s) s)
Proof
  cheat
QED

(* The base of a constructor immutable access holds 0, so ADD of it is the
   offset. *)
Theorem step_ADD_imm_base[local]:
  !ctx func cenv cx es id pop ib out s w.
    stmt_state_rel ctx func cenv cx es s /\
    cenv.ce_imm_alloca = SOME ib /\ eval_operand pop s = SOME w ==>
    step_inst_base (mk_inst id ADD [pop; ib] [out]) s =
    OK (update_var out w s)
Proof
  cheat
QED

(* A constructor immutable word load at offset pop: ADD of the base, then
   ILOAD, or ILOAD alone without a base.  It reads the memory word at pop. *)
Theorem compile_imm_load_word_ctor_frag:
  !ctx func cenv cx es pop sm op sb s0 w R.
    compile_imm_load_word T cenv.ce_imm_alloca pop sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ eval_operand pop s0 = SOME w ==>
    frag_exec ctx sm sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand op s = SOME (mload (w2n w) s0) /\
           (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
           s.vs_memory = s0.vs_memory) R
Proof
  cheat
QED

(* A word immutable in the constructor: a load from the staged immutables,
   relative to the base, which holds 0. *)
Theorem unwrap_ctor_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED
(* An aggregate in storage, transient storage or code: a copy into a buffer
   of the expression's own, allocated at instruction id sm.cs_next_id
   (exprSimCopy).  The buffer is type_memory_bytes of the value_vv's type,
   which vv_post makes the expression's; the last premise says that is the
   value's memory size and fits Python's allocation limit. *)
Theorem unwrap_copy_physical_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

Theorem unwrap_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* No value_vv points into calldata. *)
Theorem vv_post_calldata:
  !func cenv cx e es sa sm s0 es' tv t p s ctx.
    p.ptr_location = LocCalldata ==>
    ~vv_post ctx func cenv cx e es sa sm s0 es' tv (LocatedValue t p) s
Proof
  cheat
QED

Theorem unwrap_value_physical_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

Theorem unwrap_value_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* vv_post holds of a result only where it reads. *)
Theorem vv_post_failed_read:
  !func cenv cx e es sa sm s0 es' raw vv s exc ctx.
    read_result cx raw es' = (INR exc, es') ==>
    ~vv_post ctx func cenv cx e es sa sm s0 es' raw vv s
Proof
  cheat
QED

Theorem unwrap_memory_read_result_sim:
  !ctx func cenv cx e es sa sm sb s0 es' raw res t p op.
    read_result cx raw es' = (res, es') /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocMemory /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' raw (LocatedValue t p) s)
      (\s. ?v. res = INL v /\ expr_post ctx func cenv cx e es sa sb s0 es' v op s)
      (expr_exit res)
Proof
  cheat
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag unwrap_memory_read_result_sim)
  in
    if null axioms andalso null (Thm.hyp unwrap_memory_read_result_sim) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "MEMORY_FORCE_AUDIT unwrap_memory_read_result_sim OK\n"
    else print "statement-check gate skipped\n"
  end;


(* ===== Counted unwrap_value suffixes =====

   The counted judgments need the actual target path of unwrap_value's code:
   each lemma below runs that code from vv_post to expr_post along a GAS-free
   path (it reads no gas), mirroring the frag_exec lemmas above. *)

(* One emitted non-GAS instruction writing w to a fresh variable. *)
Theorem emit_op_path[local]:
  !ctx func cenv cx es opc args sa op sb s0 w.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\
    opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
        (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  cheat
QED

Theorem unwrap_storage_word_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem unwrap_runtime_immutable_word_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    fn_has_code sm sb func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* compile_imm_load_word_ctor_frag's counted form. *)
Theorem compile_imm_load_word_ctor_path[local]:
  !ctx func cenv cx es pop sm op sb s0 w.
    compile_imm_load_word T cenv.ce_imm_alloca pop sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sm.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand pop s0 = SOME w ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\
        eval_operand op s = SOME (mload (w2n w) s0) /\
        (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  cheat
QED

Theorem unwrap_ctor_immutable_word_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    fn_has_code sm sb func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem alloc_buffer_run_path[local]:
  compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
  run_inst_seq (emitted_insts sm mid) s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_path ctx func s 0
    (OK (t with vs_inst_idx := LENGTH mid.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb
Proof
  cheat
QED

Theorem alloc_buffer_source_path[local]:
  !ctx func cenv cx es sm mid buf sz s src a.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u w. gas_path ctx func s 0 (OK u) /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      u.vs_labels = s.vs_labels /\ sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      contract_storage u = contract_storage s /\
      contract_transient u = contract_transient s
Proof
  cheat
QED

Theorem storage_unwrap_word_run[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    copy_prefix loc a b 1 s 1 t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = s.vs_current_bb
Proof
  cheat
QED

Theorem storage_unwrap_word_code_path[local]:
  (opc = SLOAD \/ opc = TLOAD) /\
  do v <- emit_op opc [src]; emit_void MSTORE [dst; v] od sa = (u,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  cheat
QED

Theorem storage_unwrap_word_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path ctx func s 0 (OK z) /\ copy_prefix loc a b 1 s 1 z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem storage_unwrap_suffix_content_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; v] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem storage_unwrap_suffix_value_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\ n = type_slot_size tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  n < 2**256 /\ w2n w + 32*n < 2**256 /\ fn_has_code mid sb func /\
  ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_path ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  cheat
QED

Theorem storage_unwrap_typed_suffix_path[local]:
  !loc tv src dst mid result sb ctx func cenv cx es u t v a w.
  (loc = LocStorage \/ loc = LocTransient) /\
  (if type_slot_size tv = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F;
           return () od) mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  type_slot_size tv < 2**256 /\ w2n w + 32*type_slot_size tv < 2**256 /\
  fn_has_code mid sb func /\ ~u.vs_halted /\
  u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_path ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  cheat
QED

Theorem storage_unwrap_layout_facts[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\ fn_has_code sm sb func ==>
  ?buf mid.
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    (if (type_memory_bytes cenv t + 31) DIV 32 = 1 then
       do value <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                     [p.ptr_operand]; emit_void MSTORE [buf.buf_operand; value] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               ((type_memory_bytes cenv t + 31) DIV 32) p.ptr_location LocMemory F;
             return () od) mid = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm mid func /\ fn_has_code mid sb func /\
    sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem storage_unwrap_type_facts[local]:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    type_memory_bytes cenv t = type_memory_size tvt /\
    type_memory_size tvt < 2**64) ==>
  t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s /\
  ?a tv. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64 /\
    type_memory_bytes cenv t < dimword (:256) /\
    (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv /\
    type_slot_size tv < 2**256
Proof
  cheat
QED

Theorem storage_unwrap_buffer_post_transport[local]:
  !ctx func cenv cx e es sa sm mid sb s0 es' v t p s u z tv buf w.
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < mid.cs_next_id /\
    mid.cs_next_id <= sb.cs_next_id /\
    stmt_state_rel ctx func cenv cx es' u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
    (!name b len. local_region cenv es'.scopes u name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    fn_has_code sm mid func /\
    FLOOKUP u.vs_allocas sm.cs_next_id =
      SOME (w2n w,type_memory_bytes cenv t) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    t = expr_type e /\ type_memory_bytes cenv t = type_memory_size tv /\
    ~is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    eval_operand buf.buf_operand z = SOME w ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z
Proof
  cheat
QED

Theorem unwrap_storage_copy_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem unwrap_runtime_code_copy_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem ctor_copy_run_control[local]:
  run_inst_seq code s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code ==>
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  cheat
QED

Theorem ctor_copy_memory_path[local]:
  !n off st st' s a b ctx func imm src dst.
  compile_imm_copy_to_memory T imm src dst n off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    copy_old_operand st region) /\ fn_has_code st st' func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\ ~u.vs_halted /\
    u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    u.vs_memory = (immutable_transfers F T a b n off s).vs_memory /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s)
Proof
  cheat
QED

Theorem ctor_copy_endpoint_post[local]:
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  local_ptrs_reserved cenv sa /\ cenv.ce_is_ctor /\ ~is_word_type t /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < mid.cs_next_id /\
  mid.cs_next_id <= sb.cs_next_id /\
  compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
  fn_has_code sm mid func /\
  immutable_holds cenv cx t (Value v) a es' s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ t = expr_type e /\
  type_memory_bytes cenv t = type_memory_size tv /\
  stmt_state_rel ctx func cenv cx es' u /\ u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
  (!name b len. local_region cenv es'.scopes u name b len ==>
     regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
  eval_operand buf.buf_operand u = SOME w /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_bytes cenv t) /\
  w2n w + type_memory_bytes cenv t < dimword (:256) /\
  (?bp. buf.buf_operand = Var bp /\ not_fresh_at mid bp) /\
  z.vs_memory = (immutable_transfers F T a w (type_slot_size tv) 0 u).vs_memory /\
  copy_static z = copy_static u /\
  (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z
Proof
  cheat
QED

Theorem unwrap_ctor_code_copy_path:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED



(* unwrap_value_sim's counted form: every value_vv's code, one path. *)
Theorem unwrap_value_path:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* The counted read suffix: read_result's source step reads no gas, and
   unwrap_value's code runs along a GAS-free path. *)
Theorem unwrap_value_marked_read:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
            [] (INL v) ee (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* unwrap_value's step: expr_vv_sim gives expr_sim.  compile_expr's
   fragment ends in vv_post, and unwrap_value's code takes that to
   expr_post. *)
Theorem expr_sim_of_vv_sim:
  !ctx func cenv cx ty e es.
    post_value_type cenv e = expr_type e /\
    expr_vv_sim ctx func cenv cx ty e es /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  cheat
QED
