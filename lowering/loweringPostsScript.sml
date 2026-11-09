(* Shared pure value, place, statement and memory posts.
   These definitions precede gas certificates and simulation judgments. *)
Theory loweringPosts
Ancestors
  list rich_list finite_map pred_set pair words
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext vyperValue vyperAST
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState vyperLookupStorage vyperStorageBackend accountsRelProps
Libs
  monadsyntax

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
   bytes; for any other value, type_memory_size tv.  A
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
           BaseTV (BytesT (Dynamic _)) => 32 + LENGTH bs
         | _ => type_memory_size tv)
    | StringV str =>
        (case tv of
           BaseTV (StringT _) => 32 + LENGTH str
         | _ => type_memory_size tv)
    | _ => type_memory_size tv
End

(* ===== Offsets in a local's memory ===== *)

(* mem_field_offset, mem_step_offset and mem_path_offset are in
   loweringStateRelDefs, where local_ptrs_rel uses them. *)

(* The cenv twin of mem_step_offset and mem_path_offset, over declared
   types and read off the compile environment alone: a field sits at
   struct_field_offset of its struct's ce_struct_fields entry, as
   attr_offset places it, an element at its index times the element type's
   type_memory_bytes.  Under expr_sim_inv a path's offset here is its
   mem_path_offset in the evaluated type (type_path_offset_mem, in
   exprSimAttributeFields). *)
Definition type_step_offset_def:
  type_step_offset cenv (StructT nsid) (AttrSubscript id) =
    (let fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid)
     in OPTION_MAP (\(fty,sz). (struct_field_offset fields id, fty))
          (ALOOKUP fields id)) /\
  type_step_offset cenv (ArrayT et (Fixed n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then
       SOME (Num i * type_memory_bytes cenv et, et)
     else NONE) /\
  type_step_offset cenv (ArrayT et (Dynamic n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then
       SOME (32 + Num i * type_memory_bytes cenv et, et)
     else NONE) /\
  type_step_offset cenv (TupleT tys) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < LENGTH tys then
       SOME (SUM (MAP (type_memory_bytes cenv) (TAKE (Num i) tys)),
             EL (Num i) tys)
     else NONE) /\
  type_step_offset cenv _ _ = NONE
End

Definition type_path_offset_def:
  type_path_offset cenv t [] = SOME (0n,t) /\
  type_path_offset cenv t (sb::path) =
    case type_step_offset cenv t sb of
    | NONE => NONE
    | SOME (k,et) =>
        OPTION_MAP (\(k',pt). (k + k',pt)) (type_path_offset cenv et path)
End

(* k is the offset of a dynamic array's length word in the local n's
   region: a path through n's declared type reaches a dynamic array at k,
   k = 0 for a dynamic array local itself. *)
Definition dynarray_len_at_def:
  dynarray_len_at cenv n k <=>
    ?t0 path et m.
      cenv.ce_var_type n = SOME t0 /\
      type_path_offset cenv t0 path = SOME (k, ArrayT et (Dynamic m))
End

(* A value of type tv sits at offset k of the local n's region: a path
   through the type value of n's declared type reaches tv at k. *)
Definition local_path_at_def:
  local_path_at cenv cx n k tv <=>
    ?t0 tv0 path.
      cenv.ce_var_type n = SOME t0 /\
      evaluate_type (get_tenv cx) t0 = SOME tv0 /\
      mem_path_offset tv0 path = SOME (k, tv)
End

(* A value v of type tv sits at offset k of the local n's region: where
   local_path_at puts tv, or, for a base value (a bytestring convert
   reinterprets one in place), where it puts a base type whose bytes cover
   v's. *)
Definition local_val_at_def:
  local_val_at cenv cx n k tv v <=>
    local_path_at cenv cx n k tv \/
    ?bt bt0. tv = BaseTV bt /\ local_path_at cenv cx n k (BaseTV bt0) /\
             val_footprint tv v <= type_memory_size (BaseTV bt0)
End

(* No path through tv reaches a dynamic array: no part of a value of type
   tv is a length word that a pop writes. *)
Definition dynarray_free_def:
  dynarray_free tv <=>
    !path k etv m. mem_path_offset tv path <> SOME (k, ArrayTV etv (Dynamic m))
End

(* ===== The posts ===== *)

(* Code run from s0 to s leaves the live locals' memory alone, but for the
   length words of their dynamic arrays: the bytes of every live local's
   region at es apart from each dynamic array length word inside it
   (dynarray_len_at, the root's and the nested ones') are kept.  The only
   memory of a local an expression writes is the length word of the array
   a pop pops (exprSimPop for a local x.pop(); a pop on a nested place,
   x.f.pop() or x[i].pop(), writes the length word at its offset in x's
   declared type). *)
Definition locals_kept_def:
  locals_kept cenv es s0 s <=>
    !n b sz off len.
      local_region cenv es.scopes s0 n b sz /\ b <= off /\
      off + len <= b + sz /\
      (!k. dynarray_len_at cenv n k ==> off + len <= b + k \/ b + k + 32 <= off) ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
End

(* Where the value v of an expression of type t, lowered from compile state
   sa to sb, sits in s when t is not a word type: well formed for its type
   (val_wf), and its val_footprint bytes lie inside
   - an allocation of one of the expression's own ALLOCAs (instruction id
     in [sa.cs_next_id, sb.cs_next_id)), clear of every live local's
     region, or
   - the region of a live local at es, at the offset of a path through
     the local's declared type that reaches the value's type (the local
     itself, a field or element of it, or the element a pop popped) or,
     for a base value, a base type covering its bytes (a bytestring
     convert keeps its operand's pointer) (local_val_at),
   or it occupies no bytes (a NoneV, the result of send, has
   val_footprint 0 and sits nowhere: the lowering hands out Lit 0w).
   An operator's proof needs this to keep a first operand's value through
   the second operand's fragment: an allocation of the first is below the
   second's start counter and clear of the live locals, and expr_post
   keeps such allocations' bytes;
   a local's region it keeps but for its dynamic arrays' length words
   (locals_kept), which the path keeps apart from a value with no dynamic
   array in it. *)
Definition wb_frame_def:
  wb_frame cenv es sa s0 s <=>
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
                     local_val_at cenv cx n (w2n w - b) tv v) \/
           val_footprint tv v = 0)
End

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
   live locals' regions kept but for their dynamic arrays' length words
   (locals_kept), so a value an earlier operand left in a local survives
   too, where it covers no such word (expr_val_at). *)
Definition expr_post_def:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s <=>
    stmt_state_rel ctx func cenv cx es' s /\
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

(* The slot w holds the value obtained by reading the captured source
   result at es, the slots it occupies are in range (slots_in_range):
   a word's slot holds its value's encoding, so a load of the slot gives
   the value's word, and s's storage or transient storage agrees with the
   source's on those slots, but at the bytes the value itself leaves dead
   (storage_range_agree).  A read of a declared region has that from
   storage_rel and transient_rel; a popped element, past its array's new
   length, keeps it though its slots are dead in the array. *)
Definition storage_holds_def:
  storage_holds cx is_transient t tv (w:bytes32) es s <=>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_storage_slot cx is_transient w tvt es = (INL v, es) /\
            read_result cx tv es = (INL v, es) /\
            slots_in_range (get_storage cx es is_transient) (w2n w) tvt /\
            storage_range_agree (get_storage cx es is_transient)
              (if is_transient then contract_transient s
               else contract_storage s) w tvt
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
   lowered, and tv is the value of type t that sits there: either inside
   the immutable's value at es (sub_layout), where immutables_rel says the
   Venom state keeps it, or, in the constructor, in the staged immutables
   buffer of s within the immutable's bytes.  The second form is for an
   element popped from an array inside the immutable: it is past the
   array's new length, so no longer part of the immutable's value, but the
   pop leaves its bytes in the buffer, as storage's pop leaves its dead
   slots (storage_holds).  The immutable's bytes end below 2 ** 256, so a
   load reads at off + k itself.  No invariant gives that bound yet:
   immutables_rel at runtime bounds the offset only by the data section's
   length, so a producer of a code pointer needs a compile-env clause
   bounding ImmutableLoc offsets. *)
Definition immutable_holds_def:
  immutable_holds cenv cx t tv (w:bytes32) (es:evaluation_state)
                  (s:venom_state) <=>
    ?name off itv iv k tvt v.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module, name) =
        SOME (ImmutableLoc off) /\ w = n2w (off + k) /\
      off + type_memory_size itv < dimword (:256) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                 NONE => FEMPTY
               | SOME imms => get_source_immutables cenv.ce_module imms)
              name = SOME (itv, iv) /\
      evaluate_type (get_tenv cx) t = SOME tvt /\
      (sub_layout itv iv k tvt v \/
       cenv.ce_is_ctor /\ k + type_memory_size tvt <= type_memory_size itv /\
       val_in_memory tvt v (off + k) s.vs_memory) /\
      value_has_type tvt v /\
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
         | LocStorage => storage_holds cx F t tv w es s
         | LocTransient => storage_holds cx T t tv w es s
         | LocCode => immutable_holds cenv cx t tv w es s
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
                      local_val_at cenv cx n (w2n w - b) tvt v) \/
            val_footprint tvt v = 0))
End

(* expr_post with a value_vv in place of an operand. *)
Definition vv_post_def:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s <=>
    stmt_state_rel ctx func cenv cx es' s /\
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

(* The location of a storage or transient place. *)
Definition slot_loc_def:
  slot_loc tr = if tr then LocTransient else LocStorage
End

(* w is where the lowering finds the source place pv of type vt, at
   location loc, in s (see the header).  A local's place is at its pointer
   plus the path's offset in its declared type. *)
Definition place_ptr_rel_def:
  (place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc vt <=>
     ?p sz b t0 tv0 k tv t.
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
       lookup_var p s = SOME b /\
       cenv.ce_var_type id = SOME t0 /\
       evaluate_type (get_tenv cx) t0 = SOME tv0 /\
       mem_path_offset tv0 path = SOME (k,tv) /\
       w = b + n2w k /\ loc = SOME LocMemory /\
       vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\
     ?t. vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (HashMapRef tr slot kt vt') w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\ vt = HashMapT kt vt') /\
  (place_ptr_rel cenv cx s (PlaceR (ImmutablePlace src id path)) w loc vt <=>
     F) /\
  (place_ptr_rel cenv cx s (Value v) w loc vt <=> F)
End

(* A local's place reads at es: extending it can fail only by a type
   error.  A place is formed where it reads, but an index evaluated after
   the base can pop the base's array (x[i][x[i].pop()]). *)
Definition place_readable_def:
  (place_readable cx es (PlaceR (MemoryPlace id path)) <=>
     ?v. read_place cx (MemoryPlace id path) es = (INL v,es)) /\
  (place_readable cx es pv <=> T)
End

(* After the target's fragment, run from s0 related at es, in s related at
   es', with the source's place pv of type vt: the pointer r's operand is
   at pv, and r's place type is vt's.  The operand is not fresh at the
   fragment's end, so code lowered after it keeps it.  The frame is
   vv_post's: the variables and allocations from before, the memory of the
   allocations made before the fragment's start but those holding a local,
   and the live locals' memory but their dynamic arrays' length words
   (locals_kept), the root's and the nested ones'. *)
Definition target_post_def:
  target_post ctx func cenv cx es sa sb s0 es' pv vt
    (r : operand # data_location option # place_ty option) s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    (?w. eval_operand (FST r) s = SOME w /\
         place_ptr_rel cenv cx s pv w (FST (SND r)) vt) /\
    SND (SND r) = SOME (value_type_place vt) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    place_readable cx es' pv /\
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

(* compile_stmts, returning the compile environment after the list's
   declarations. *)
Definition stmts_env_def:
  stmts_env cenv lctx ty [] = return cenv /\
  stmts_env cenv lctx ty (s::ss) =
    do cs <- comp_get;
       if block_is_terminated cs then return cenv
       else
         do cenv' <- declare_stmt_local cenv s;
            compile_stmt cenv' lctx ty s;
            stmts_env cenv' lctx ty ss
         od
    od
End

(* A statement with its declaration, as compile_stmts compiles it,
   returning the compile environment after the declaration. *)
Definition stmt_env_def:
  stmt_env cenv lctx ty s =
    do cenv' <- declare_stmt_local cenv s;
       compile_stmt cenv' lctx ty s;
       return cenv'
    od
End

(* Where the code of a fragment from sa to sb leaves off on an outcome
   that does not exit: its end, or the start of the loop's exit or
   increment block. *)
Definition stmt_lands_def:
  stmt_lands lctx (sb : compile_state) (res : unit + exception) s <=>
    (res = INL () /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?ex inc. lctx = InLoop ex inc /\ s.vs_inst_idx = 0 /\
       ((res = INR BreakException /\ s.vs_current_bb = ex) \/
        (res = INR ContinueException /\ s.vs_current_bb = inc)))
End

(* cenv' is cenv with bindings changed only for names of locals (unbound
   or held through a pointer on both sides) that the scopes below the
   innermost do not hold: the declarations of the innermost scope, and
   names out of scope.  Leaving the innermost scope goes back to cenv
   (stmt_state_rel_pop_top_ext).  Of the other fields only ce_var_type and
   ce_dynarray_capacity may differ, for any name. *)
Definition cenv_top_ext_def:
  cenv_top_ext cenv cenv' (scopes : (string |-> scope_entry) list) <=>
    cenv' with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
                  ce_dynarray_capacity := cenv.ce_dynarray_capacity |> =
      cenv /\
    !n. FLOOKUP cenv'.ce_vars n <> FLOOKUP cenv.ce_vars n ==>
        (!l. FLOOKUP cenv.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        (!l. FLOOKUP cenv'.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        ?sc rest. scopes = sc :: rest /\ lookup_scopes n rest = NONE
End

(* The return PC of an internal function's frame (ce_return_pc, the
   variable RETPC_PARAM binds at the function's entry) is defined, and it
   was handed out before sa, so stmt_frag's frame on old variables keeps
   it.  RET reads it; an external function has none. *)
Definition ret_pc_ok_def:
  ret_pc_ok cenv sa s <=>
    !x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x /\ ?w. lookup_var x s = SOME w
End

(* The size in ce_return_buf describes a pointer slot.  Capacity below is
   the actual caller allocation, supplied by the declared return layout. *)
Definition return_buf_frame_def:
  (return_buf_frame NONE (cenv : compile_env) sa s <=>
    cenv.ce_return_buf = NONE) /\
  (return_buf_frame (SOME (bw : bytes32, capacity)) cenv sa s <=>
    ?x slot_size.
      cenv.ce_return_buf = SOME (PtrVar (Var x) slot_size) /\
      lookup_var x s = SOME bw /\ not_fresh_at sa x /\
      w2n bw + capacity <= s.vs_alloca_next)
End
