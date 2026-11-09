Theory bodyPtrIfExpAllocProbe
Ancestors
  bodyPtrDefs exprLowering context compileEnv loweringHalt

(* These are allocation-before-unwrap compiler equations, not a counted
   execution theorem. Stack and non-word memory operands emit no unwrap
   instructions: the freshly allocated destination cannot be disturbed.
   Other locations still require a local counted unwrap/frame interface. *)
Theorem ifexp_allocated_stack_arm:
  !ce rt st vt op sa tmp sb sc.
    ~is_word_type rt /\ ~same_memory_layout ce st rt /\
    compile_alloc_buffer (type_memory_bytes ce rt) sa = (tmp,sb) /\
    compile_store_memory ce op tmp.buf_operand rt st sb = ((),sc) ==>
    compile_ifexp_arm ce rt st (StackValue vt op) sa =
      (tmp.buf_operand,sc)
Proof
  rpt strip_tac >>
  simp[compile_ifexp_arm_def, unwrap_value_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

Theorem ifexp_allocated_memory_arm:
  !ce rt st vt p sa tmp sb sc.
    ~is_word_type rt /\ ~same_memory_layout ce st rt /\
    ~is_word_type vt /\ p.ptr_location = LocMemory /\
    compile_alloc_buffer (type_memory_bytes ce rt) sa = (tmp,sb) /\
    compile_store_memory ce p.ptr_operand tmp.buf_operand rt st sb = ((),sc) ==>
    compile_ifexp_arm ce rt st (LocatedValue vt p) sa =
      (tmp.buf_operand,sc)
Proof
  rpt strip_tac >>
  simp[compile_ifexp_arm_def, unwrap_value_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

(* General ghost-frame coverage boundary: no assertion of unchanged memory
   is needed for coverage itself. To instantiate after a real unwrap, the
   missing local interface must supply ghost_kept and operand preservation. *)
Theorem ptr_covers_ghost_kept:
  !ce es sa G0 tn0 s0 G tn s p n.
    ghost_kept ce es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
    lookup_var p s = lookup_var p s0 /\ ptr_covers G0 tn0 p s0 n ==>
    ptr_covers G tn p s n
Proof
  rpt strip_tac >> gvs[ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

(* Checked allocation/unwrap frame instance. The two genuinely local unwrap
   premises are ghost_kept at sb (not sa) and preservation of the allocated
   variable. expr_sim_ptr_of_vv is a whole-expression theorem and does not
   itself supply these for an isolated unwrap after an inserted allocation. *)
Theorem ifexp_allocated_buffer_frame[local]:
  !ce es sa buf sb G0 tn0 s0 G tn s p n.
    compile_alloc_buffer n sa = (buf,sb) /\ buf.buf_operand = Var p /\
    ghost_kept ce es sb G0 tn0 s0 G tn /\
    lookup_var p s = lookup_var p s0 /\ ptr_covers G0 tn0 p s0 n ==>
    ptr_covers G tn p s n
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >>
  drule_all ptr_covers_ghost_kept >> simp[]
QED

(* Actual store dispatch inventory (contextScript.sml:671-808,835-842):
   Top-level word destination is excluded by the allocating-arm guard.
   Bytes/string destination uses compile_store_bytestring, independent of
   source tag. Non-bytes differing types use compile_store_memory_typed;
   equal types use fixed compile_copy_memory. Typed dispatch includes:
   - word: MLOAD/MSTORE (source clean word, two covered windows);
   - bytes/string pair: runtime padded copy, clean source length word;
   - cyclic metadata: INVALID (exceptional counted exit, not normal copy);
   - dynamic arrays: clean length, capacity ASSERT, header MSTORE, then
     dynamic MCOPY for equal elements/strides or a recursive element loop;
   - fixed arrays: static copy for equal elements/strides, else recursive loop;
   - tuples: recursive paired fields, empty side terminates;
   - structs: recursive name lookup and accumulated source/destination offsets;
   - other pairs: fixed destination-size copy, needing source coverage of
     that size, not just coverage at source lowered size.
   No reachability exclusion for recursive aggregate cases has been proved.
   Existing compile_store_bytestring_gas_path_ptr supplies counted execution
   only after runtime header cleanliness, padded extent, source/destination
   coverage, old operand variables and instruction-prefix premises hold.
   compile_alloc_buffer_expr_resources supplies robust preservation and
   coverage for an ALLOCA step, but not its counted path, ghost_inv or a
   local unwrap summary. Those are separate remaining interfaces. *)
