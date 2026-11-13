(* C1.34.6.72.4.3.1: contract report, NOT an asserted recursive theorem. *)
Theory extRetRecursiveContractAuditPtr
Ancestors extRetRobustSourceChildrenPtr extRetSourceAllocationPtr

(* PROPOSED CONTRACT SCHEMA (unverified; no new predicate is defined).

   Fix env,ty,tv,v,ei,src,dst,scap,dcap and an allocation schedule A.
   For compile_abi_encode_to_buf (Var dst) (Var src) ei sa = (out,sb),
   the intended conclusion has the following HOL shape:

   ?Gf tnf sf n.
     gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
     sf.vs_current_bb = sb.cs_current_bb /\
     sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
     eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
     n <= dcap /\
     (!av. vyper_to_abi env ty v = SOME av ==>
       mem_bytes_at (w2n b) n sf.vs_memory =
         enc (vyper_to_abi_type env ty) av) /\
     (!i. w2n b <= i /\ i < w2n b+n ==> i NOTIN tnf.t_mem) /\
     (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
       val_in_memory tv v (w2n a) mem') /\
     (!p. not_fresh_at sa p ==>
       lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p)) /\
     mem_agree_outside W sf.vs_memory s.vs_memory /\
     (!i. i NOTIN W ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
     tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans

   Here a,b are entry operand words, W is the union of the destination
   writable envelope and every scratch span in A, INCLUDING newly allocated
   spans even if only partly written. No outside-destination frame is valid
   for a branch which initializes scratch. Allocation metadata persistence,
   alloca_inv, non-memory effect frames and final ptr_covers for old source
   and destination operands must also be retained by the eventual contract.
   The displayed endpoint is a schema, not a sufficient premise list.

   Entry: actual plan/evaluation/typing/conversion; robust fixed v in every
   permitted memory; code/PC/nonhalted, no DAlloca, operand reservation;
   source and destination coverage and branch-specific strict arithmetic
   bounds. For zero reads omit source Var/provenance. For each scratch site
   the schedule must provide its actual address, size 32, strict end bound,
   disjointness from source reads, destination, and live ancestor scratch.
   Neither existence nor caller production of this schedule is proved here.
   A static aggregate source uses declared capacity; bytes/string use live
   length+32, not declared capacity. The endpoint's single av implication is
   functional source conversion, not an ABI representative uniform in memory.

   INDUCTION: mirror compile_abi_encode_child_ind's mutual compiler recursion,
   with the lexicographic measure explicitly used in abiEncoderScript.sml
   lines 383-392: plan size and dispatcher rank; complex member-list size.
   Runtime dynamic-array iteration additionally needs induction on remaining
   LENGTH vs-i, with a counted backedge invariant. Compiler induction alone
   does not execute the runtime loop.

   BRANCH MATRIX: abiEncoderScript.sml lines 230-382.
   * AbiPrimWord: read [src,src+32), write [dst,dst+32), result 32;
     no scratch, robust primitive word cleanliness. Existing static counted
     leaf is extRetAbiStaticCountedPtr; needs coverage/address bounds and
     memory/taint frames. Does not require fresh child allocation.
   * AbiCopy k: read/write k bytes, result k, no scratch; zero k is zero-read
     and must not acquire provenance by assumption. Existing counted bulk
     copy tools apply; generic source static-clean/size producer still has
     to select the appropriate leaf from plan/evaluation.
   * AbiBytestring: read 32+live bytes, first zero final output word at
     dst+ceil32 live, then MCOPY; result 32+ceil32 live. No scratch.
     compile_abi_encode_bytes_live_ambient_counted_ptr (extRetAbiBytesLivePtr
     lines 24-60) already supplies exact memory, taint, old-register frame,
     source preservation and coverage. Its strict source/destination end
     bounds, disjointness and robust ABI-input premises must be produced.
     Root empty bytes still reads a length word and writes 32 bytes.
   * AbiDynArray static element: parent cursor32 initialized to zero, then
     length MLOAD/MSTORE; static loop allocates index32 even at length zero;
     result 32+len*asz, parent cursor updated/reloaded. Children use
     src+32+i*msz and dst+32+i*asz. Existing
     compile_abi_encode_dyn_static_loop_counted_ptr (array static counted
     lines 184-219) proves ONLY the inner loop. It requires fixed robust ABI
     input, explicit scratch address/exclusion, clean destination header,
     strict full-span bounds. It exports no general exterior memory/taint
     frame, so cannot yet be substituted as the generic recursive child.
   * AbiDynArray dynamic element: parent cursor32, index32, tail cursor32;
     head extent len*asz after destination length word, tail starts there.
     Each iteration recursively writes at dst+32+cursor, then writes head
     offset, updates cursor and index. Source child is fixed EL i vs at
     src+32+i*msz (robust_dynamic_source_child). Length word clean by
     robust_dynamic_source_length_clean. Missing counted dynamic-loop
     invariant retaining parent/index/tail cells through nested allocations,
     destination initialized head prefix/tail prefix, and offset+len bounds.
     On length zero loop still allocates scratch but does not read children.
   * AbiComplex []: no reads/writes/scratch, literal zero result; no source
     allocation witness. Type evaluation can reject some empty-element arrays
     but that cannot justify adding a read to this compiler branch.
   * AbiComplex nonempty static: no own scratch, constant total head size;
     each child src+SUM prior mem_sz, dst+SUM prior abi_sz. Children may be
     zero-sized; inherited source provenance only needed for positive reads.
     Existing robust tuple/struct/sparse projections supply semantic memory,
     NOT offset arithmetic/provenance. Need generalized child/static frames.
   * AbiComplex dynamic: allocate cursor32, initialize total head size;
     traverse children, reload cursor. Each dynamic child MLOADs cursor,
     encodes at dst+cursor, writes static head offset and updates cursor.
     Static child writes its own head directly and leaves cursor untouched.
     Generalize singleton prefix/suffix boundaries to arbitrary offsets and
     cursor values, with cap-cursor remaining capacity and strict additions.
   * compile_abi_encode_child: always emits head ADD, even for static child
     and zero offset. Dynamic case must preserve head/cursor/off operands
     across recursive call, and keep cursor memory clean. Singleton ambient
     prefix (singleton counted lines 157-181) is specialized to head offset 0,
     cursor value32; suffix (218-242) stores head32 and cursor32 and has exact
     taint difference. These are not generic child frame theorems.

   CALL-SITE / FRAME AUDIT AND MISSING OBLIGATIONS.
   1. stmtLoweringScript.sml 368-372 allocates ce_max_return_size and invokes
      encoder. frame_valued_return_capacity_word_bound proves literal size
      < dimword from actual Return guard, NOT positive source/end bounds.
      compile_alloc_buffer_state_counted_ptr (extRetBufferStatePtr 50-80)
      produces strict destination end, coverage, stmt_state_rel, old-register
      frame and alloca registration persistence, assuming not_local_ptr and
      distinct ids. This is an actual producer for destination allocation,
      not for generic encoder scratch budget.
   2. prospective_alloca_expr_interval_disjoint excludes actual source
      footprint from a specified future allocation, given source expr_val_at,
      site membership, id interval and not_local_ptr. Nonbytes capacity
      equals footprint; bytes/string exclusion is live-only. Its hypotheses
      must be transported to all nested scratch sites, including reused loop
      sites; robust child representation alone does not preserve expr_val_at.
   3. allocaSiteResource$alloca_site_registered_disjoint and
      alloca_site_preserved_protection can separate destination/ancestor
      scratch from distinct registered child sites, given alloca_inv and
      registration persistence. Fresh site protection additionally needs
      protected end <= allocation frontier. Reused sites need actual
      membership/size plus id distinctness. Missing counted allocation/frame
      boundary that threads these facts recursively; no need to edit toolkit.
   4. abiEncoderProps enc_frame already uses output UNION fragment scratch
      footprint; enc_pre requires full capacity below lo and top<dimword.
      Those are stronger than current live-only bytes producer. Semantic
      abi_encoder_owned_scratch_frame / head_scratch_footprint in
      abiEncoderChildEffect and address_scratch_disjoint in
      abiEncoderScratchTransport are bookkeeping aids, not counted ptr/taint
      proofs. The new invariant must include taint framing on the same union
      and separately protect live ancestor scratch cells outside child union.
   5. Equality to dimword is NOT accepted by bytes/static-array counted
      interfaces. Strict destination allocation end has a producer in (1).
      Source coverage alone gives no strict endpoint. Need a branch-sensitive
      source-read strict-bound producer or a checked relaxation of task-owned
      leaves; do not assume full bytes capacity below dimword. Child pointer
      ADD/MUL provenance and bounds remain missing. Zero-read descendants
      must avoid artificial strict source/provenance premises.
   6. Fixed-v memory projections are ready. General plan-to-child typing,
      offset-size and encoded-length/remaining-capacity arithmetic still need
      producer lemmas. Existing static-array loop fixed-av premise cannot be
      instantiated from pointwise open_input by exchanging quantifiers.
      Need a source-indexed specialization or restricted leaf bridge.

   Verdict: no counterexample established; proposed general contract is NOT
   validated. Finite missing interfaces are source read strict bounds/offset
   provenance, source-indexed static-loop frame, generic child prefix/suffix,
   allocation-schedule/ancestor scratch preservation, and dynamic loop counted
   invariant. No protected file change is required by this audit.
*)
