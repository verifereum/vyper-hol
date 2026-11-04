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
 *   val_store_size, val_store_size_le, val_footprint_le_store_size — the
 *                            bytes storing a value writes: a bytestring's
 *                            data rounded up to whole words
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
 * Helpers: expr_exit_INL, expr_exit_success_map, expr_val_at_start_mono,
 *   typed_val_to_w256_word_value, eval_expr_env,
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
 * no other value on such a length word.  The counted judgments select
 * source readings from the actual target GAS prefix before checking these
 * posts.
 *
 * Not covered by the leaves here:
 *   - bytes and string literals: a bytesN literal is a Lit of its typed
 *     encoding, a dynamic bytes or string literal a memory buffer;
 *   - locals other than word_value ones (address, bytesN, memory-backed);
 *   - block.prevhash: evaluate_block_hash raises a RuntimeError when the
 *     block number is 0 or the hash list is too short, while Venom's
 *     BLOCKHASH is total, so the lowered code does not abort there; and
 *     call_ctx_rel does not relate bc_blockhash to the transaction's block
 *     hashes.  expr_sim is unprovable for it as things stand.
 * The msg.gas leaf is proved separately in msgGasPost.
 * Nor does the memory frame in expr_post follow from stmt_state_rel for an
 * expression whose lowering writes a DALLOCA buffer (raw_call of msg.data,
 * the create copy and blueprint lowerings): DALLOCA allocates at vs_fmp,
 * which stmt_state_rel does not relate to the ALLOCA allocations.
 *)

Theory exprSim
Ancestors
  exprSimProps
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
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




(* Exit predicates are insensitive to the successful result representation. *)


(* The source results the judgment speaks of: a value, an error other than
   a type error, or an assertion.  Type errors and control exceptions
   (break, continue, return) are left out. *)


(* The value v of an expression of type t held by operand op in s: a word
   type's value as the operand, in the typed word encoding of t (the one
   the lowering uses for address and bytesN), any other type's value in
   memory at the operand's address, as val_in_memory lays it out.  The
   lowering makes the same split: unwrap_value loads a word type and hands
   out the pointer of any other.  Nothing is said where t does not
   evaluate. *)

(* The bytes from its address that the value v of type tv occupies in
   memory: for a dynamic bytes or string value, its length word and its data
   bytes; for any other value, type_memory_size tv.  A
   bytes or string literal's annotation is the type it is used at (Bytes[100]
   for a literal of 3 bytes assigned to a Bytes[100] local), while the
   lowering, like Python's _lower_bytelike, allocates a buffer the size of
   the literal's own length, so expr_val_at bounds a value by this and not
   by its type's size.  val_in_memory reads no more than these bytes
   (val_in_memory_footprint_agree). *)

(* The bytes from its address that storing the value v of type tv writes
   (compile_store_memory): for a dynamic bytes or string value, its length
   word and its data rounded up to whole words, as compile_store_bytestring
   copies them; for any other value, type_memory_size tv. *)

(* A dynamic array type: its memory layout starts with the length word. *)

(* The local n is a dynamic array, by the compile environment's type of it,
   which expr_sim_inv makes the local's type. *)

(* Code run from s0 to s leaves the live locals' memory alone, but for the
   length word of a dynamic array local: the bytes of every live local's
   region at es, from its second word on for a dynamic array, are kept.
   The only memory of a local an expression writes is the length word of
   the array x.pop() pops (exprSimPop).  A pop on a nested place
   (x.f.pop(), x[i].pop()) would write a length word inside the region,
   which this frame does not exempt; its lowering is wrong as it stands
   (exprSimPlaces's compile_pop_other_sim), and lowering it right means
   exempting the length words of nested dynamic arrays here too. *)





(* Locals kept up to s, then whole regions kept from s to t. *)

(* Code that keeps every live local's whole region keeps the locals. *)

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


(* Operand composition: the value of a non-word operand survives code that
   keeps the operand and the bytes of the value's footprint, the
   type_memory_size bytes at its address (val_in_memory_mem_agree). *)

(* A dynamic bytes value's data fits in its rounded-up words. *)

(* Rounding down to whole words: clearing the low five bits. *)


(* The dynamic bytestrings, where footprint and store size are their own;
   every other value takes its type's size. *)

(* A well-formed value's footprint fits its type's size. *)

(* A value's footprint is within the bytes storing it writes. *)

(* A well-formed value's store size fits its type's size. *)

(* val_in_memory reads no more than the value's footprint. *)

(* Operand composition at the footprint expr_val_at bounds: the value of a
   non-word operand survives code that keeps the operand and its
   val_footprint bytes. *)

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

(* The fragment of e lowered as a value of type ty, run from a state
   related at es, the source state where e is evaluated, under the code
   premises of the statement lemmas.  On a value it reaches its end in
   expr_post; on an error other than a type error or an assertion it exits
   as expr_exit allows.  This is expr_frag (loweringSlice) with the failing
   outcomes added. *)


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

(* tvt v sits at offset k inside the layout of itv iv: wherever memory holds
   iv, it holds v k bytes further on, inside iv's bytes.  A struct's field
   sits so in the struct, and any value at offset 0 in itself. *)

(* w points k bytes into the data of an immutable of the module being
   lowered, and tv is the value of type t that sits there (sub_layout)
   inside the immutable's value at es; immutables_rel says where the Venom
   state keeps that value.  The immutable's bytes end below 2 ** 256, so a
   load reads at off + k itself.  No invariant gives that bound yet:
   immutables_rel at runtime bounds the offset only by the data section's
   length, so a producer of a code pointer needs a compile-env clause
   bounding ImmutableLoc offsets. *)

(* A compiled value holds the value read from the captured source result
   at es.  Located values retain their expression type and location;
   memory words also retain their typed encoding.  No current compiler
   case returns a calldata pointer. *)

(* Where a value in memory sits, as expr_val_at says for expr_post: for a
   StackValue, expr_val_at itself; for a pointer into memory, the value's
   bytes inside one of the expression's own allocations or a live local's
   region, word types included, unless it occupies none. *)

(* expr_post with a value_vv in place of an operand. *)

(* Raw expression results include values and captured places.  Mapping
   roots are excluded because they cannot be read as values. *)




(* expr_sim with compile_expr in place of lower_value: compile_expr's
   fragment of e, run from a state related at es, reaches its end with the
   value_vv holding the source result as vv_post says, or exits as
   expr_exit allows. *)


(* Where compile_expr hands out a StackValue, unwrap_value emits no code, so
   expr_sim is expr_vv_sim on the results that are values. *)


(* expr_sim gives expr_frag where the expression's type is a word type
   whose typed encoding agrees, on the values the expression evaluates to,
   with val_to_w256, the encoding expr_frag uses. *)


(* An expression whose results the judgment speaks of are all values: its
   fragment need only reach expr_post. *)


(* ===== stmt_state_rel and the variables ===== *)

(* stmt_state_rel reads the variables only through the pointers of the
   live locals. *)



(* ===== Leaves ===== *)


(* A value of a word type in memory: its word is the typed encoding. *)

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



(* Environment reads with their annotated types; block.prevhash and
   msg.gas use separate leaf lemmas. *)
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
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                `\s. stmt_state_rel ctx func cenv cx es s /\
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
  simp[step_inst_base_opcode_eqs, exec_read0_def, exec_gas_def, venomInstTheory.mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
     val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]
QED
