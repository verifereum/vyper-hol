(*
 * Expression simulation in the unit context (#636, part 1)
 *
 * The judgment expr_sim: the fragment of an expression, run from
 * stmt_state_rel at the source state where the expression is evaluated,
 * either reaches its end with stmt_state_rel at the source state after it
 * and the operand holding its value (expr_post), or, where the source
 * raises an error other than a type error or an assertion, exits with an
 * Abort as result_rel allows.
 *
 * TOP-LEVEL:
 *   expr_exit, expr_res_ok, expr_val_rel, expr_val_at, expr_post,
 *   expr_sim
 *   expr_sim_values        — expr_sim of an expression whose results are
 *                            values, from its fragment reaching expr_post
 *   expr_sim_expr_frag     — expr_sim gives loweringSlice's expr_frag
 *   stmt_state_rel_vars_frame, stmt_state_rel_vars_ext,
 *   stmt_state_rel_drop_fresh — stmt_state_rel reads the variables only
 *                            through the live locals' pointers
 *   compile_literal_word_sim — bool, integer and decimal literals
 *   compile_name_word_sim  — a word local
 *   compile_env_sim        — environment reads (msg.sender, block.number,
 *                            ...), all but block.prevhash and msg.gas
 *   expr_val_rel_mem_agree — a non-word operand's value survives code that
 *                            keeps its type_memory_size bytes
 *   val_footprint, val_footprint_le, val_in_memory_footprint_agree,
 *   expr_val_rel_footprint_agree — the bytes a memory value occupies, which
 *                            expr_val_at bounds, and the same at them
 *   val_in_memory_word_type — a word type's value in memory: its word is
 *                            the typed encoding
 *   dynarray_type, dynarray_local, locals_kept — the frame on the live
 *                            locals' memory in expr_post: every byte of a
 *                            live local's region is kept, but a DynArray
 *                            local's length word
 *   locals_kept_mem, locals_kept_mem_tail, locals_kept_regions,
 *   locals_kept_regions_tail — locals_kept from equal memory or from the
 *                            whole regions kept, and along such code
 *   locals_kept_refl, locals_kept_inst_idx — reflexivity and instruction-index
 *                            normalization of the local frame
 *
 * Helpers: expr_exit_INL, typed_val_to_w256_word_value, eval_expr_env,
 *   lower_value_env
 *
 * Values are related by expr_val_rel, by the expression's type: a word
 * type's value as the operand in the typed encoding typed_val_to_w256, any
 * other type's value in memory at the operand, as val_in_memory has it.
 * expr_val_at says where a memory-backed value's bytes are: in one of the
 * expression's own allocations or in a live local's region.  expr_post
 * keeps the memory of the allocations made before the fragment's start,
 * but its own and the live locals'.  So two operands lowered in turn
 * compose where the first one's value sits in a buffer it allocated: that
 * allocation's id is below the second's start counter and it holds no
 * local (alloca_inv, local_backed), so the second's expr_post keeps its
 * bytes, and val_in_memory with them (expr_val_rel_footprint_agree:
 * expr_val_at bounds the value's val_footprint bytes).  expr_post also
 * keeps the bytes of the live locals at its start (locals_kept), but the
 * length word of a DynArray local, which x.pop() writes; expr_val_at puts
 * no other value on such a length word.  expr_frag,
 * which relates values by val_to_w256, follows for a word type whose typed
 * encoding is val_to_w256 (expr_sim_expr_frag).
 *
 * Not covered by the leaves here:
 *   - bytes and string literals: a bytesN literal is a Lit of its typed
 *     encoding, a dynamic bytes or string literal a memory buffer;
 *   - locals other than word_value ones (address, bytesN, memory-backed);
 *   - block.prevhash: evaluate_block_hash raises a RuntimeError when the
 *     block number is 0 or the hash list is too short, while Venom's
 *     BLOCKHASH is total, so the lowered code does not abort there; and
 *     call_ctx_rel does not relate bc_blockhash to the transaction's block
 *     hashes.  expr_sim is unprovable for it as things stand;
 *   - msg.gas: the source reads the next of the state's gas readings
 *     (gas_obs), while the lowering emits GAS, and call_ctx_rel does not
 *     relate the two.
 * Nor does the memory frame in expr_post follow from stmt_state_rel for an
 * expression whose lowering writes a DALLOCA buffer (raw_call of msg.data,
 * the create copy and blueprint lowerings): DALLOCA allocates at vs_fmp,
 * which stmt_state_rel does not relate to the ALLOCA allocations.
 *)

Theory exprSim
Ancestors
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

(* ===== The judgment ===== *)

(* The exits a source result allows: an error other than a type error
   (a runtime error, or the revert of a failed external call, create or
   raw_call) any Abort, an assertion a revert, or an exceptional halt for
   "UNREACHABLE", as result_rel relates them.  external_call_result_rel
   asks a revert for RevertData, but result_rel, which the statement lemmas
   conclude, allows any Abort. *)
Definition expr_exit_def:
  (expr_exit (INR (Error (RuntimeError m))) (Abort a s) <=> T) /\
  (expr_exit (INR (Error (RevertData d))) (Abort a s) <=> T) /\
  (expr_exit (INR (AssertException str)) (Abort a s) <=>
     a = Revert_abort \/ (a = ExHalt_abort /\ str = "UNREACHABLE")) /\
  (expr_exit _ _ <=> F)
End

Theorem expr_exit_INL[simp]:
  !x r. ~expr_exit (INL x) r
Proof
  Cases_on `r` >> simp[expr_exit_def]
QED

(* The source results the judgment speaks of: a value, an error other than
   a type error, or an assertion.  Type errors and control exceptions
   (break, continue, return) are left out. *)
Definition expr_res_ok_def:
  expr_res_ok (res : value + exception) <=>
    (?v. res = INL v) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

(* The value v of an expression of type t held by operand op in s: a word
   type's value as the operand, in the typed word encoding of t (the one
   the lowering uses for address and bytesN), any other type's value in
   memory at the operand's address, as val_in_memory lays it out.  The
   lowering makes the same split: unwrap_value loads a word type and hands
   out the pointer of any other.  Nothing is said where t does not
   evaluate. *)
Definition expr_val_rel_def:
  expr_val_rel cx t v op s <=>
    ?w. eval_operand op s = SOME w /\
        !tv. evaluate_type (get_tenv cx) t = SOME tv ==>
             if is_word_type t then w = typed_val_to_w256 tv v
             else val_in_memory tv v (w2n w) s.vs_memory
End

(* The bytes from its address that the value v of type tv occupies in
   memory: for a dynamic bytes or string value, its length word and its data
   rounded up to whole words; for any other value, type_memory_size tv.  A
   bytes or string literal's annotation is the type it is used at (Bytes[100]
   for a literal of 3 bytes assigned to a Bytes[100] local), while the
   lowering, like Python's _lower_bytelike, allocates a buffer the size of
   the literal's own length, so expr_val_at bounds a value by this and not
   by its type's size.  val_in_memory reads no more than these bytes
   (val_in_memory_footprint_agree). *)
Definition val_footprint_def:
  val_footprint tv v =
    case v of
      BytesV bs =>
        (case tv of
           BaseTV (BytesT (Dynamic _)) => 32 + 32 * word_size (LENGTH bs)
         | _ => type_memory_size tv)
    | StringV str =>
        (case tv of
           BaseTV (StringT _) => 32 + 32 * word_size (LENGTH str)
         | _ => type_memory_size tv)
    | _ => type_memory_size tv
End

(* A dynamic array type: its memory layout starts with the length word. *)
Definition dynarray_type_def:
  dynarray_type t <=> ?et n. t = ArrayT et (Dynamic n)
End

(* The local n is a dynamic array, by the compile environment's type of it,
   which expr_sim_inv makes the local's type. *)
Definition dynarray_local_def:
  dynarray_local cenv n <=> ?t. cenv.ce_var_type n = SOME t /\ dynarray_type t
End

(* Code run from s0 to s leaves the live locals' memory alone, but for the
   length word of a dynamic array local: the bytes of every live local's
   region at es, from its second word on for a dynamic array, are kept.
   The only memory of a local an expression writes is the length word of
   the array x.pop() pops (exprSimPop).  A pop on a nested place
   (x.f.pop(), x[i].pop()) would write a length word inside the region,
   which this frame does not exempt; its lowering is wrong as it stands
   (exprSimPlaces's compile_pop_other_sim), and lowering it right means
   exempting the length words of nested dynamic arrays here too. *)
Definition locals_kept_def:
  locals_kept cenv es s0 s <=>
    !n b sz off len.
      local_region cenv es.scopes s0 n b sz /\ b <= off /\
      off + len <= b + sz /\ (dynarray_local cenv n ==> b + 32 <= off) ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
End

Theorem locals_kept_mem_tail:
  !cenv es s0 t u.
    locals_kept cenv es s0 t /\ u.vs_memory = t.vs_memory ==>
    locals_kept cenv es s0 u
Proof
  rw[locals_kept_def]
QED

Theorem locals_kept_refl[simp]:
  !cenv es s. locals_kept cenv es s s
Proof
  simp[locals_kept_def]
QED

Theorem locals_kept_mem:
  !cenv es s0 s. s.vs_memory = s0.vs_memory ==> locals_kept cenv es s0 s
Proof
  metis_tac[locals_kept_mem_tail, locals_kept_refl]
QED

Theorem locals_kept_inst_idx[simp]:
  !cenv es s0 s k.
    locals_kept cenv es s0 (s with vs_inst_idx := k) <=>
    locals_kept cenv es s0 s
Proof
  simp[locals_kept_def]
QED

(* Locals kept up to s, then whole regions kept from s to t. *)
Theorem locals_kept_regions_tail:
  !cenv es s0 s t.
    locals_kept cenv es s0 s /\
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
    locals_kept cenv es s0 t
Proof
  rw[locals_kept_def] >>
  qpat_x_assum `!n b sz. local_region _ _ _ n b sz ==> _` drule >>
  strip_tac >>
  drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`off`, `len`] mp_tac) >>
  impl_tac >- decide_tac >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* Code that keeps every live local's whole region keeps the locals. *)
Theorem locals_kept_regions:
  !cenv es s0 s.
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) ==>
    locals_kept cenv es s0 s
Proof
  metis_tac[locals_kept_regions_tail, locals_kept_refl]
QED

(* Where the value v of an expression of type t, lowered from compile state
   sa to sb, sits in s when t is not a word type: well formed for its type
   (val_wf), and its val_footprint bytes lie inside
   - an allocation of one of the expression's own ALLOCAs (instruction id
     in [sa.cs_next_id, sb.cs_next_id)), clear of every live local's
     region, or
   - the region of a live local at es, past its length word where the
     local is a dynamic array and t is not (an element, or the popped one,
     of the array; the array itself starts at the length word),
   or it occupies no bytes (a NoneV, the result of send, has
   val_footprint 0 and sits nowhere: the lowering hands out Lit 0w).
   An operator's proof needs this to keep a first operand's value through
   the second operand's fragment: an allocation of the first is below the
   second's start counter and clear of the live locals, and expr_post
   keeps such allocations' bytes;
   a local's region it keeps but for a dynamic array's length word
   (locals_kept). *)
Definition expr_val_at_def:
  expr_val_at cenv cx t sa sb es v op s <=>
    !tv. evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t ==>
      val_wf tv v /\
      ?w. eval_operand op s = SOME w /\
          ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
                       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                       b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
                       (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                                   b + sz <= lb \/ lb + lsz <= b)) \/
           (?n b sz. local_region cenv es.scopes s n b sz /\
                     b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
                     (dynarray_local cenv n /\ ~dynarray_type t ==>
                      b + 32 <= w2n w)) \/
           val_footprint tv v = 0)
End

(* Operand composition: the value of a non-word operand survives code that
   keeps the operand and the bytes of the value's footprint, the
   type_memory_size bytes at its address (val_in_memory_mem_agree). *)
Theorem expr_val_rel_mem_agree:
  !cx t v op s s' w tv.
    expr_val_rel cx t v op s /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ val_wf tv v /\
    mem_bytes_at (w2n w) (type_memory_size tv) s.vs_memory =
      mem_bytes_at (w2n w) (type_memory_size tv) s'.vs_memory ==>
    expr_val_rel cx t v op s'
Proof
  rw[expr_val_rel_def] >> gvs[] >>
  qspecl_then [`tv`, `v`, `w2n w`, `type_memory_size tv`, `s.vs_memory`,
               `s'.vs_memory`] mp_tac
    valueEncodingPropsTheory.val_in_memory_mem_agree >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

(* A dynamic bytes value's data fits in its rounded-up words. *)
Theorem le_word_size_mul:
  !n. n <= 32 * word_size n
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  `(n + 31) MOD 32 < 32` by simp[] >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >> decide_tac
QED

Theorem word_size_le_of_le_mul[local]:
  !len k. len <= 32 * k ==> word_size len <= k
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  `(32 * k + 31) DIV 32 = k` by
    (once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  `(len + 31) DIV 32 <= (32 * k + 31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  gvs[]
QED

(* A well-formed value's footprint fits its type's size. *)
Theorem val_footprint_le:
  !tv v. val_wf tv v ==> val_footprint tv v <= type_memory_size tv
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    (Cases_on `v` >> simp[val_footprint_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[]))
  >- (gvs[val_footprint_def, valueEncodingTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      irule word_size_le_of_le_mul >> simp[])
  >- (gvs[val_footprint_def, valueEncodingTheory.val_wf_def,
          valueEncodingTheory.type_memory_size_def] >>
      irule word_size_le_of_le_mul >> simp[]) >>
  simp[]
QED

(* val_in_memory reads no more than the value's footprint. *)
Theorem val_in_memory_footprint_agree:
  !tv v off mem mem'.
    val_in_memory tv v off mem /\ val_wf tv v /\
    mem_bytes_at off (val_footprint tv v) mem =
      mem_bytes_at off (val_footprint tv v) mem' ==>
    val_in_memory tv v off mem'
Proof
  rpt strip_tac >>
  `(?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
   (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
   val_footprint tv v = type_memory_size tv` by
    (Cases_on `v` >> simp[val_footprint_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[]))
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >>
      `LENGTH bs <= 32 * word_size (LENGTH bs)` by simp[le_word_size_mul] >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH bs) mem' =
       mem_bytes_at (off + 32) (LENGTH bs) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >>
      simp[])
  >- (gvs[val_footprint_def, val_in_memory_def] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >>
      `LENGTH str <= 32 * word_size (LENGTH str)` by simp[le_word_size_mul] >>
      `mem_word_at off mem' = mem_word_at off mem` by
        (qpat_x_assum `!off2. _ ==> mem_word_at _ _ = _` irule >> simp[]) >>
      `mem_bytes_at (off + 32) (LENGTH str) mem' =
       mem_bytes_at (off + 32) (LENGTH str) mem` by
        (qpat_x_assum `!off2 len2. _ ==> mem_bytes_at _ _ _ = _` irule >>
         simp[]) >>
      simp[]) >>
  qpat_x_assum `val_footprint _ _ = _` (fn th => fs[th]) >>
  qspecl_then [`tv`, `v`, `off`, `type_memory_size tv`, `mem`, `mem'`]
    mp_tac valueEncodingPropsTheory.val_in_memory_mem_agree >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

(* Operand composition at the footprint expr_val_at bounds: the value of a
   non-word operand survives code that keeps the operand and its
   val_footprint bytes. *)
Theorem expr_val_rel_footprint_agree:
  !cx t v op s s' w tv.
    expr_val_rel cx t v op s /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ eval_operand op s' = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ val_wf tv v /\
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory ==>
    expr_val_rel cx t v op s'
Proof
  rw[expr_val_rel_def] >> gvs[] >>
  irule val_in_memory_footprint_agree >> simp[] >>
  qexists_tac `s.vs_memory` >> simp[]
QED

(* Where the fragment of e that started in s0, related at es, lowered from
   compile state sa to sb, ends when the source gives v and es': related at
   es', the operand op holding v (and, for a memory-backed value, placed as
   expr_val_at says), the variables handed out before sa and the
   allocations of s0 kept, and the memory of the allocations of s0 kept,
   but for two kinds:
   - those of e's own ALLOCAs (instruction id sa.cs_next_id or above): an
     ALLOCA run again, in a loop body, returns its earlier buffer, which e
     then writes again;
   - those holding a live local: e can write a local (x.pop()), and
     stmt_state_rel at es' says what the locals hold.
   The rest are the buffers of the expressions lowered before e, so a
   value an earlier operand left in memory survives e's fragment.  And the
   live locals' regions kept but for a dynamic array's length word
   (locals_kept), so a value an earlier operand left in a local survives
   too, where it does not cover that word (expr_val_at). *)
Definition expr_post_def:
  expr_post func cenv cx e es sa sb s0 es' v op s <=>
    stmt_state_rel func cenv cx es' s /\
    expr_val_rel cx (expr_type e) v op s /\
    expr_val_at cenv cx (expr_type e) sa sb es' v op s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

(* The fragment of e lowered as a value of type ty, run from a state
   related at es, the source state where e is evaluated, under the code
   premises of the statement lemmas.  On a value it reaches its end in
   expr_post; on an error other than a type error or an assertion it exits
   as expr_exit allows.  This is expr_frag (loweringSlice) with the failing
   outcomes added. *)
Definition expr_sim_def:
  expr_sim ctx func cenv cx ty e es <=>
    !sa sb op res es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      (do result <- eval_expr cx e; read_result cx result od) es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
        (\s. ?v. res = INL v /\
                 expr_post func cenv cx e es sa sb s0 es' v op s)
        (expr_exit res)
End

(* ===== The judgment on compile_expr's value ===== *)

(* expr_sim speaks of lower_value: compile_expr's code and then
   unwrap_value's, run as one piece.  A case that lowers an operand with
   compile_expr and unwraps it later, after code of its own (the elements
   of a struct or array literal, the arguments of an external call), or
   never (len, in on an array), needs what compile_expr's value_vv holds
   when compile_expr's code ends.  expr_vv_sim says that; expr_sim follows
   from it and unwrap_value's code (exprSimHyps). *)

(* The slot w holds the value obtained by reading the captured source
   result at es, the slots it occupies are in range (slots_in_range):
   a word's slot holds its value's encoding, so a load of the slot gives
   the value's word, and the read sees no other value's dead bytes, so
   storage_rel and transient_rel relate the Venom slots it reads. *)
Definition storage_holds_def:
  storage_holds cx is_transient t tv (w:bytes32) es <=>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_storage_slot cx is_transient w tvt es = (INL v, es) /\
            read_result cx tv es = (INL v, es) /\
            slots_in_range (get_storage cx es is_transient) (w2n w) tvt /\
            storage_read_live cx is_transient (get_storage cx es is_transient)
              w tvt
End

(* tvt v sits at offset k inside the layout of itv iv: wherever memory holds
   iv, it holds v k bytes further on, inside iv's bytes.  A struct's field
   sits so in the struct, and any value at offset 0 in itself. *)
Definition sub_layout_def:
  sub_layout itv iv k tvt v <=>
    k + type_memory_size tvt <= type_memory_size itv /\
    !b mem. val_in_memory itv iv b mem ==> val_in_memory tvt v (b + k) mem
End

(* w points k bytes into the data of an immutable of the module being
   lowered, and tv is the value of type t that sits there (sub_layout)
   inside the immutable's value at es; immutables_rel says where the Venom
   state keeps that value.  The immutable's bytes end below 2 ** 256, so a
   load reads at off + k itself.  No invariant gives that bound yet:
   immutables_rel at runtime bounds the offset only by the data section's
   length, so a producer of a code pointer needs a compile-env clause
   bounding ImmutableLoc offsets. *)
Definition immutable_holds_def:
  immutable_holds cenv cx t tv (w:bytes32) (es:evaluation_state) <=>
    ?name off itv iv k tvt v.
      FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module, name)) =
        SOME (ImmutableLoc off) /\ w = n2w (off + k) /\
      off + type_memory_size itv < dimword (:256) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                 NONE => FEMPTY
               | SOME imms => get_source_immutables cenv.ce_module imms)
              name = SOME (itv, iv) /\
      evaluate_type (get_tenv cx) t = SOME tvt /\
      sub_layout itv iv k tvt v /\ value_has_type tvt v /\
      read_result cx tv es = (INL v, es)
End

(* A compiled value holds the value read from the captured source result
   at es.  Located values retain their expression type and location;
   memory words also retain their typed encoding.  No current compiler
   case returns a calldata pointer. *)
Definition vv_holds_def:
  (vv_holds cenv cx t tv (StackValue t' op) es s <=>
     ?v. read_result cx tv es = (INL v, es) /\ expr_val_rel cx t v op s) /\
  (vv_holds cenv cx t tv (LocatedValue t' p) es s <=>
     t' = t /\
     ?w. eval_operand p.ptr_operand s = SOME w /\
         case p.ptr_location of
           LocMemory =>
             ?v. read_result cx tv es = (INL v, es) /\
                 !tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
                       val_in_memory tvt v (w2n w) s.vs_memory /\
                       (is_word_type t ==>
                        mem_word_at (w2n w) s.vs_memory =
                          typed_val_to_w256 tvt v)
         | LocStorage => storage_holds cx F t tv w es
         | LocTransient => storage_holds cx T t tv w es
         | LocCode => immutable_holds cenv cx t tv w es
         | LocCalldata => F)
End

(* Where a value in memory sits, as expr_val_at says for expr_post: for a
   StackValue, expr_val_at itself; for a pointer into memory, the value's
   bytes inside one of the expression's own allocations or a live local's
   region, word types included, unless it occupies none. *)
Definition vv_at_def:
  (vv_at cenv cx t sa sb es tv (StackValue t' op) s <=>
     !v. read_result cx tv es = (INL v, es) ==> expr_val_at cenv cx t sa sb es v op s) /\
  (vv_at cenv cx t sa sb es tv (LocatedValue t' p) s <=>
     p.ptr_location = LocMemory ==>
     !v tvt. read_result cx tv es = (INL v, es) /\
             evaluate_type (get_tenv cx) t = SOME tvt ==>
       val_wf tvt v /\
       ?w. eval_operand p.ptr_operand s = SOME w /\
           ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
                        sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                        b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                        (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                                    b + sz <= lb \/ lb + lsz <= b)) \/
            (?n b sz. local_region cenv es.scopes s n b sz /\
                      b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                      (dynarray_local cenv n /\ ~dynarray_type t ==>
                       b + 32 <= w2n w)) \/
            val_footprint tvt v = 0))
End

(* expr_post with a value_vv in place of an operand. *)
Definition vv_post_def:
  vv_post func cenv cx e es sa sb s0 es' tv vv s <=>
    stmt_state_rel func cenv cx es' s /\
    vv_holds cenv cx (expr_type e) tv vv es' s /\
    vv_at cenv cx (expr_type e) sa sb es' tv vv s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

(* Raw expression results include values and captured places.  Mapping
   roots are excluded because they cannot be read as values. *)
Definition expr_vv_res_ok_def:
  expr_vv_res_ok (res : eval_result + exception) <=>
    (?v. res = INL (Value v)) \/ (?p. res = INL (PlaceR p)) \/
    (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

Definition expr_read_res_ok_def:
  expr_read_res_ok cx es res <=>
    (?r v. res = INL r /\ read_result cx r es = (INL v,es)) \/
    (?exc. res = INR exc /\
           expr_res_ok (INR exc : value + exception))
End

(* expr_sim with compile_expr in place of lower_value: compile_expr's
   fragment of e, run from a state related at es, reaches its end with the
   value_vv holding the source result as vv_post says, or exits as
   expr_exit allows. *)
Definition expr_vv_sim_def:
  expr_vv_sim ctx func cenv cx ty e es <=>
    !sa sb vv res es' s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      eval_expr cx e es = (res, es') /\ expr_vv_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post func cenv cx e es sa sb s0 es' tv vv s)
        (expr_exit res)
End

(* Where compile_expr hands out a StackValue, unwrap_value emits no code, so
   expr_sim is expr_vv_sim on the results that are values. *)
Theorem expr_vv_sim_stack:
  !ctx func cenv cx ty e es.
    expr_sim ctx func cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!tv es'. eval_expr cx e es = (INL tv, es') ==> ?v. tv = Value v) ==>
    expr_vv_sim ctx func cenv cx ty e es
Proof
  rw[expr_vv_sim_def] >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op, sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  Cases_on `res`
  >- (rename1 `eval_expr cx e es = (INL raw, es')` >>
      `?v. raw = Value v` by metis_tac[] >> gvs[] >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o SIMP_RULE std_ss [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es'`, `s0`] mp_tac) >>
      simp[bind_def, read_result_def, return_def, expr_res_ok_def] >>
      strip_tac >> irule frag_exec_conseq >>
      first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
          read_result_def, return_def] >> first_assum ACCEPT_TAC) >>
  rename1 `eval_expr cx e es = (INR exc, es')` >>
  `expr_res_ok (INR exc : value + exception)` by
    gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INR exc`, `es'`, `s0`] mp_tac) >>
  simp[bind_def] >> strip_tac >>
  irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt gen_tac >>
  Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* expr_sim gives expr_frag where the expression's type is a word type
   whose typed encoding agrees, on the values the expression evaluates to,
   with val_to_w256, the encoding expr_frag uses. *)
Theorem expr_sim_expr_frag:
  !ctx func cenv cx ty e es R tv.
    expr_sim ctx func cenv cx ty e es /\ is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    (!v es'. (do result <- eval_expr cx e; read_result cx result od) es = (INL v, es') ==>
             typed_val_to_w256 tv v = val_to_w256 v) ==>
    expr_frag ctx func cenv cx ty e es R
Proof
  rw[expr_sim_def, expr_frag_def] >>
  first_x_assum (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es'`, `s0`]
                   mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  strip_tac >> irule frag_exec_conseq >>
  first_x_assum (irule_at Any) >>
  simp[expr_post_def, expr_val_rel_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
    (qspec_then `tv` mp_tac) >>
  qpat_x_assum `!v es'. (do result <- eval_expr _ _; read_result _ result od) _ = _ ==> _` drule >>
  gvs[]
QED

(* An expression whose results the judgment speaks of are all values: its
   fragment need only reach expr_post. *)
Theorem expr_sim_values:
  !ctx func cenv cx ty e es.
    (!res es'. (do result <- eval_expr cx e; read_result cx result od) es = (res, es') /\ expr_res_ok res ==>
               ?v. res = INL v) /\
    (!sa sb op v es' s0.
       lower_value compile_expr cenv ty e sa = (op, sb) /\
       (do result <- eval_expr cx e; read_result cx result od) es = (INL v, es') /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa ==>
       frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
         (expr_post func cenv cx e es sa sb s0 es' v op) (\r. F)) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >> simp[expr_sim_def] >> rpt strip_tac >>
  qpat_x_assum `!res es'. _ ==> _` (drule_all_then strip_assume_tac) >>
  gvs[] >>
  first_x_assum (drule_all_then (qspec_then `s0` assume_tac)) >>
  irule frag_exec_conseq >>
  first_x_assum (irule_at Any) >> simp[]
QED

(* ===== stmt_state_rel and the variables ===== *)

(* stmt_state_rel reads the variables only through the pointers of the
   live locals. *)
Theorem stmt_state_rel_vars_frame:
  !func cenv cx es s V.
    stmt_state_rel func cenv cx es s /\
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p (s with vs_vars := V) = lookup_var p s) ==>
    stmt_state_rel func cenv cx es (s with vs_vars := V)
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes (s with vs_vars := V)` by
    (irule local_ptrs_rel_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >> conj_tac
     >- metis_tac[] >>
     rpt strip_tac >> gvs[]) >>
  `alloca_inv (s with vs_vars := V)` by
    (irule alloca_inv_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `alloca_room func (s with vs_vars := V)` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
     immutables_rel_def, logs_rel_def, contract_storage_def,
     contract_transient_def] >>
  metis_tac[]
QED

Theorem stmt_state_rel_vars_ext:
  !func cenv cx es t t'.
    stmt_state_rel func cenv cx es t /\ vars_ext t t' ==>
    stmt_state_rel func cenv cx es t'
Proof
  rw[vars_ext_def] >>
  qpat_x_assum `t' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[lookup_var_def] >> metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem stmt_state_rel_drop_fresh:
  !func cenv cx es st s.
    local_ptrs_reserved cenv st ==>
    (stmt_state_rel func cenv cx es (drop_fresh st s) <=>
     stmt_state_rel func cenv cx es s)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (irule stmt_state_rel_vars_ext >> qexists_tac `drop_fresh st s` >>
      simp[vars_ext_drop_fresh]) >>
  simp[drop_fresh_def] >> irule stmt_state_rel_vars_frame >> simp[] >>
  rpt strip_tac >> simp[GSYM drop_fresh_def] >>
  irule lookup_var_drop_fresh >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* ===== Leaves ===== *)

Theorem typed_val_to_w256_word_value:
  !tv v. word_value v ==> typed_val_to_w256 tv v = val_to_w256 v
Proof
  rw[word_value_def] >> Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

(* A value of a word type in memory: its word is the typed encoding. *)
Theorem val_in_memory_word_type:
  !tenv t tvt v off mem.
    is_word_type t /\ evaluate_type tenv t = SOME tvt /\
    value_has_type tvt v /\ val_in_memory tvt v off mem ==>
    mem_word_at off mem = typed_val_to_w256 tvt v
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
      typed_val_to_w256_def]
QED

(* A word local held through its pointer (loweringSlice's
   compile_name_word_frag). *)
Theorem compile_name_word_sim:
  !ctx func cenv cx ty ann id es p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all lower_value_name_word >> strip_tac >>
  irule frag_exec_conseq >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
                           `val_to_w256 entry.value`, `\r. F`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> strip_tac >>
      drule_all step_name_word >> simp[]) >>
  strip_tac >> first_x_assum (irule_at Any) >> rpt strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      vyperASTTheory.expr_type_def,
      typed_val_to_w256_word_value, locals_kept_mem]
QED

val literal_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def];

(* A bool, integer or decimal literal annotated with a word type: a Lit,
   no code. *)
Theorem compile_literal_word_sim:
  !ctx func cenv cx ty ann l es.
    is_word_type ann /\
    ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_def] >> gvs[Once evaluate_def, bind_def, read_result_def, return_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_tac) >>
  literal_word_tac
QED

Theorem eval_expr_env:
  !cx ann item es res es'.
    (do result <- eval_expr cx (Builtin ann (Env item) []); read_result cx result od) es = (res, es') /\
    expr_res_ok res /\ item <> PrevHash /\ item <> MsgGas ==>
    es' = es /\
    ?v. res = INL v /\
        evaluate_builtin cx es.accounts ann (Env item) [] [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `item` >> fs[evaluate_builtin_def, return_def, raise_def] >>
  rw[] >> gvs[expr_res_ok_def, read_result_def, return_def]
QED

Theorem lower_value_env:
  !cenv ty ann item sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Env item) []) sa =
      (op, sb) ==>
    compile_env_var item sa = (op, sb)
Proof
  rpt gen_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def] >>
  Cases_on `compile_env_var item sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

(* An environment read (msg.sender, block.timestamp, ...) annotated with
   its type, but block.prevhash and msg.gas, for which expr_sim does not
   hold (see the header). *)
Theorem compile_env_sim:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  conj_tac >~ [`expr_res_ok _`]
  >- (rpt strip_tac >> drule_all eval_expr_env >> strip_tac >> simp[]) >>
  rpt strip_tac >>
  `expr_res_ok (INL v : value + exception)` by
    simp[expr_res_ok_def] >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  `is_word_type (env_item_type item) /\
   !tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v` by
    (Cases_on `item` >>
     gvs[evaluate_builtin_def, env_item_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
         val_to_w256_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []) >>
  drule lower_value_env >> strip_tac >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                `\s. stmt_state_rel func cenv cx es s /\
                     eval_operand op s = SOME (val_to_w256 v) /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b) /\
                     s.vs_memory = s0.vs_memory`,
                `\r. F`] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, locals_kept_mem] >>
  Cases_on `item` >>
  gvs[compile_env_var_def, evaluate_builtin_def] >>
  drule emit_op_frag >> disch_then irule >>
  simp[is_terminator_def] >> rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_read0_def, venomInstTheory.mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
     val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]
QED
