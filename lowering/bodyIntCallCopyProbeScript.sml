(* Semantic probe for deferred aggregate forcing: one copied slot, not
   aggregate layout correctness. *)
Theory bodyIntCallCopyProbe
Ancestors
  exprSimStorageCopy valueEncodingProps exprLoweringProps venomExecSemantics
  venomState venomInst emitHelperProps exprSimUnwrap

Theorem copy_slot_tload_step[local]:
  !op a id out s.
    eval_operand op s = SOME a ==>
    step_inst_base (mk_inst id TLOAD [op] [out]) s =
      OK (update_var out (tload a s) s)
Proof
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem storage_copy_slot_content_frame:
  !opc a b id out s.
    (opc = SLOAD \/ opc = TLOAD) /\
    w2n a + 1 < dimword (:256) /\ w2n b + 32 < dimword (:256) ==>
    ?t. run_inst_seq
          [mk_inst id opc [Lit a] [out];
           mk_inst (id+1) MSTORE [Lit b; Var out] []] s = OK t /\
        mem_word_at (w2n b) t.vs_memory =
          (if opc = SLOAD then sload a s else tload a s) /\
        (!off len. off + len <= w2n b \/ w2n b + 32 <= off ==>
          mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexists_tac `mstore (w2n b)
    (if opc = SLOAD then sload a s else tload a s)
    (update_var out (if opc = SLOAD then sload a s else tload a s) s)` >>
  conj_tac
  >- (`step_inst_base (mk_inst id opc [Lit a] [out]) s =
        OK (update_var out (if opc = SLOAD then sload a s else tload a s) s)` by
        (qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[]
         >- (irule step_SLOAD >> simp[eval_operand_def]) >>
         irule copy_slot_tload_step >> simp[eval_operand_def]) >>
      `step_inst_base (mk_inst (id+1) MSTORE [Lit b; Var out] [])
        (update_var out (if opc = SLOAD then sload a s else tload a s) s) =
        OK (mstore (w2n b) (if opc = SLOAD then sload a s else tload a s)
          (update_var out (if opc = SLOAD then sload a s else tload a s) s))` by
        (irule step_MSTORE >> simp[eval_operand_def, lookup_var_update_var]) >>
      simp[run_inst_seq_def]) >>
  simp[mstore_mem_word_at_same] >> conj_tac
  >- (rpt strip_tac >> irule EQ_TRANS >>
      irule_at Any mstore_mem_bytes_at_disjoint >> simp[] >>
      simp[update_var_def]) >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Integration report (proposed interfaces, NOT established by this probe).

   For the storage/transient loop, let a be the source slot word, b the
   destination byte address, n the compiler word_count, sbase the entry
   state, ds the temporary registers and cv the counter.  At the header
   after k iterations the intended invariant is the conjunction:
     k <= n /\ eval_operand (Var cv) s = SOME (n2w k) /\
     storage_copy_frame ds sbase s /\
     (!j. j < k ==> mem_word_at (b + 32*j) s.vs_memory =
       (if transient then tload (a + n2w j) sbase
        else sload (a + n2w j) sbase)) /\
     (!off len. off + len <= b \/ b + 32*n <= off ==>
       mem_bytes_at off len s.vs_memory =
       mem_bytes_at off len sbase.vs_memory).
   Also preserve storage, transient storage, allocation-map entries and
   all non-memory components required by stmt_state_rel.  The existing
   storage_copy_frame deliberately records only registers and labels.
   Full-address framing requires b + 32*n < dimword(:256); n must not
   wrap the loop counter.  Source slot addition above is intentionally
   modular: slots_in_range does NOT supply an address no-wrap bound.
   The stronger non-wrap source premise of the one-slot probe is not a
   claimed property of arbitrary storage_holds.

   Missing storage layout bridge: evaluate_type tenv t = SOME tvt,
   decode_value storage (w2n a) tvt = SOME v, slots_in_range storage
   (w2n a) tvt, and agreement of each copied slot with read_slot storage
   must imply val_in_memory tvt v b copied_memory.  This needs recursive
   tuple/array/struct and dynamic-bytes decoding, including canonical
   primitive encodings; raw copied words alone do not establish it.
   type_memory_size tvt = 32 * type_slot_size tvt must connect that
   induction to the actual compiler's type_memory_bytes and word_count.
   storage_read_live and storage_agree must supply all slots traversed by
   decoding, not only the head slot used by storage_holds_load.

   Runtime code uses compile_code_to_memory: zero words is empty, else
   compile_word_copy_loop LocCode LocMemory F, hence DLOAD (not ILOAD),
   with byte rather than slot source offsets.  The corresponding prefix
   invariant reads words at off + 32*j from vs_data_section, preserving
   the entire data section.  immutable_holds supplies a sub_layout and
   off + type_memory_size itv < dimword(:256); immutables_rel supplies
   val_in_memory of the enclosing immutable in the data section.  A
   byte-copy-to-val_in_memory transfer at that sub-layout is still needed.

   Destination room, allocation identity, local-region disjointness and
   preservation of all outstanding vv_holds/vv_at witnesses must come
   from the actual allocated buffer and caller endpoint.  The checked
   ensure_storage_memory_defined_frag does not provide these bounds or
   contents.  vv_at constrains only LocMemory values; it gives no extra
   slot bounds for storage/transient values.  None of these missing
   interfaces is an additional hypothesis on the frozen internal-call
   theorem, nor does this one-slot probe discharge aggregate forcing.
*)

(* Consumer contract for the remaining forcing development (unproved).

   Historical proposal (insufficient premises; superseded by the coverage
   audit below): drop the case restriction from unwrap_runtime_noncopy_sim.
   The originally proposed hypotheses were:
     unwrap_value cenv vv sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     ~cenv.ce_is_ctor
   and its conclusion is frag_exec ctx sm sb
     (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s)
     (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R.
   The checked noncopy boundary handles StackValue, LocMemory and word
   values; the additional obligations are precisely non-word LocStorage,
   LocTransient and LocCode (LocCalldata has false vv_post).

   The list consumer additionally needs a framed raw-result boundary.
   Given read_result cx raw es = (INL v,es), expr_sim_inv cenv cx env es,
   the same compile/freshness/runtime premises and the source vv_post
   interpreted with raw, the precondition must carry
     EVERY (\(ty,r,held,lo).
       vv_holds cenv cx ty r held es s /\
       vv_at cenv cx ty lo sm es r held s /\
       safe_operand sm (vv_operand held)) hs.
   The postcondition is expr_post of v at the new operand, conjoined with
   the same EVERY at upper boundary sb instead of sm (lo is UNCHANGED).
   This is the exact held-entry shape of vv_post_deferred_prefix; that
   theorem assumes compile_expr, not unwrap_value, and explicitly assumes
   full local-window agreement and held immutable preservation. It cannot
   supply the required frame by instantiation or from vv_post alone.  vv_post_read_result handles raw
   result interpretation but does not itself prove memory preservation.

   Dependency map: slot execution + full copied-prefix loop + allocation
   frame -> storage/transient contents; decoding/layout bridge -> typed
   storage/transient unwrap.  Runtime DLOAD loop + sub_layout byte copy
   -> code unwrap.  These plus checked noncopy -> unrestricted runtime
   unwrap.  Operand/old-allocation/local-region frame for each copy ->
   EVERY held-entry preservation -> framed raw forcing -> list staging.
   The existing successful-list endpoint supplies held entries, their
   original lo boundaries, and safe operands.  It does not supply copy
   contents, allocation bounds, or an unwrap-specific held-entry frame.
   Runtime exclusion must come from the body compile environment, and
   size bounds from actual allocation/type correspondence; neither may
   be silently postulated at the frozen call site.  Full implementation
   requires a strategist-owned decomposition beyond this diagnostic.
*)

(* Runtime code-copy diagnostic (C1.6.2.12.6; contracts NOT yet proved).

   Proposed compile_code_to_memory_content_frag:
     compile_code_to_memory src dst n sa = (u,sb) /\
     (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
     eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
     n < dimword (:256) /\ w2n a + 32*n < dimword (:256) /\
     w2n b + 32*n < dimword (:256)
   ==> frag_exec ctx sa sb (\s. s = sbase)
     (\s. mem_bytes_at (w2n b) (32*n) s.vs_memory =
             mem_bytes_at (w2n a) (32*n) sbase.vs_data_section /\
       (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
         mem_bytes_at off len s.vs_memory =
           mem_bytes_at off len sbase.vs_memory) /\
       (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
       s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
         vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
         vs_inst_idx := sbase.vs_inst_idx|> = sbase) R.

   The n=0 branch is compiler return (), not a generated counted loop.
   For n>0 the source and destination scales are BOTH 32. DLOAD reads
   TAKE 32 (DROP (w2n (a+n2w (32*j))) data ++ REPLICATE 32 0w).
   Source bound above turns this into the natural byte window at
   w2n a+32*j; no requirement that data actually has that many bytes is
   needed for padded contents. Destination bound makes each MSTORE
   natural and disjoint from the previously copied prefix. Prefix word
   equalities must still be assembled into the displayed byte equality.
   The complete data section is preserved by the record-restoration clause.

   No new general relocation theorem is needed: use the EXISTING
   valueEncodingPropsTheory.val_in_memory_relocate, whose premises are
     val_in_memory tv v src mem /\ val_wf tv v /\
     type_memory_size tv <= n /\
     mem_bytes_at src n mem = mem_bytes_at dst n mem'.
   valueCopyTheory.val_in_memory_relocate instead uses val_footprint and
   reversed window equality; exprSimMemoryTransport has a footprint-only
   equality interface too. Do not duplicate any of these.

   Actual runtime instantiation: immutable_holds gives off,itv,iv,k,tvt,v
   with a=n2w(off+k), off+type_memory_size itv < dimword(:256),
   evaluate_type (get_tenv cx) ty = SOME tvt, sub_layout itv iv k tvt v,
   value_has_type tvt v, and the immutable lookup. immutables_rel at
   cenv.ce_module, cx.txn.target and is_ctor=F gives
     val_in_memory itv iv off sbase.vs_data_section
   plus off+type_memory_size itv <= LENGTH sbase.vs_data_section.
   sub_layout then yields val_in_memory tvt v (off+k) data and
   k+type_memory_size tvt <= type_memory_size itv. Obtain val_wf from
   value_has_type, and apply relocation directly to this SUBVALUE, not to
   the enclosing immutable. No sub_layout relocation theorem is required.

   expr_sim_inv_memory_size gives mem_bytes=type_memory_size tvt;
   type_memory_size_slots gives type_memory_size tvt=32*type_slot_size tvt.
   Hence n=(mem_bytes+31) DIV 32=type_slot_size tvt and 32*n=mem_bytes:
   copying does not extend beyond the enclosing immutable even at its
   last sub-layout. Thus off+k+32*n < dimword(:256), w2n a=off+k,
   and n<dimword(:256). Destination bound remains the allocation consumer's
   obligation; it does NOT follow from immutable_holds or sub_layout.
   Runtime immutables_rel must be extracted from stmt_state_rel with the
   actual compile environment; constructor memory is not a data section.
   This diagnostic neither proves the DLOAD loop nor allocation framing.
*)

(* Allocation/held-entry diagnostic (C1.6.2.12.7; NOT a proof).

   For non-word LocStorage, LocTransient or LocCode, unwrap_value calls
   compile_ensure_in_memory, whose FIRST instruction is compile_alloc_buffer
   mem_bytes at sm.cs_next_id, with output Var (% ++ toString sm.cs_next_var).
   compile_alloc_buffer_insts identifies the operand and exact requested
   size; compile_alloc_buffer_fresh_frag proves the fresh execution formula.
   However, NONE at that allocation id does NOT follow from vv_post,
   local_ptrs_reserved or increasing compile ids: vv_post permits replayed
   allocations. A correct semantic boundary must handle BOTH ALLOCA cases.

   Fresh: alloca_room_fresh gives base+mem_bytes<dimword(:256), provided
   this ALLOCA belongs to func and mem_bytes<dimword(:256). The latter
   requires expr_sim_inv_memory_size plus actual alloc_limits_expr/type
   capacity facts; it is NOT a consequence of the unrestricted vv_post.
   local_ptrs_rel_exec_alloca_fresh supplies identity and local separation,
   using not_local_ptr from local_ptrs_reserved and compile var freshness.
   alloca_inv gives separation from all previous tracked allocations.
   Replay: stmt_state_rel's per-instruction size clause identifies the
   recorded size, alloca_inv bounds its end by the frontier and separates
   distinct ids. fn_inst_ids_distinct plus reserved local-pointer outputs
   must exclude this instruction from a live local's backing ALLOCA;
   borrowed locals are disjoint from EVERY recorded allocation by
   local_backed. A held temporary has aid<sm.cs_next_id by vv_at, so it
   cannot use this allocation's id. Reuse these cases rather than assuming
   that every unwrap ALLOCA is fresh.

   Missing at the formerly proposed unrestricted boundary (lines 110-118):
   fn_has_code sm sb func, fn_inst_ids_distinct func, the actual size bound
   mem_bytes<dimword(:256), and type/layout correspondence. frag_exec's
   own fn_has_code refers to a quantified executing function, not necessarily
   the func in stmt_state_rel. Therefore the old contract is not justified
   by the advertised premises. These facts exist at expression/body callers
   but must be threaded by an authorized interface repair, not presumed.

   Consumer-matching single-entry target, under the repaired runtime unwrap
   hypotheses and read_result cx raw es'=(INL v,es'):
   frag_exec ctx sm sb
     (\s. vv_post ctx func cenv cx e es sa sm s0 es' raw vv s /\
       vv_holds cenv cx ty r held es' s /\
       vv_at cenv cx ty lo sm es' r held s /\
       safe_operand sm (vv_operand held))
     (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
       vv_holds cenv cx ty r held es' s /\
       vv_at cenv cx ty lo sb es' r held s /\
       safe_operand sb (vv_operand held)) R.
   lo is unchanged. The EVERY target replaces the last three conjuncts
   by EVERY (\(ty,r,held,lo). ...same three conjuncts...) hs at each end.
   The old-variable frame preserves held operands; immutable/storage holds
   use unchanged data/storage/transient fields; LocMemory uses disjoint
   copy framing on its vv_at allocation or live-local window. Stack holds
   may themselves encode memory, so also use expr_val_at/val_footprint
   framing, not merely operand equality. vv_at_region_frame and
   local_region_pointer_frame handle allocation-map inclusion and local
   pointer preservation. vv_post_read_result covers raw inputs without
   changing the read source state. EVERY then lifts the SAME single-entry
   frame over hs, retaining each original lo. Neither the existing
   vv_post_deferred_prefix (compile_expr only) nor this diagnostic proves it.
*)

(* Readiness audit (C1.6.2.12.8).
   CHECKED: unwrap_runtime_noncopy_sim handles StackValue, LocMemory and
   word values only. compile_storage_copy_content_frag proves modular
   SLOAD/TLOAD word contents, disjoint byte-window frame, old registers and
   record restoration, but requires destination room/counter bounds and
   does not identify any typed value. Existing type_memory_size_slots,
   expr_sim_inv_memory_size and val_in_memory_relocate are reusable, not
   missing obligations. vv_post_deferred_prefix is a conditional consumer for
   expression evaluation, not forcing; it is not an unwrap composition
   theorem. The SAME counted execution must still supply local-window
   agreement, immutable preservation, and storage/transient frames jointly.

   UNPROVED semantic outputs, in dependency order:
   - decoder-to-memory transfer for all type_value branches, including
     sparse/default arrays, tuples, structs, canonical scalars and bytes;
     its exact-slot premise must be supplied via a live-byte-aware
     source/target storage bridge, NOT original-source full-slot equality;
   - DLOAD counted-copy content/frame, including compiler's zero branch,
     with the exact contract above; existing relocation then handles code;
   - allocation identity/separation/room for both fresh and replay ALLOCA,
     with actual-function code membership, distinct ids and size facts;
   - runtime clean aggregate unwrap combining contents, typed transfer,
     allocation, stmt_state_rel and expr_post frames; repair the proposed
     unrestricted interface above to carry missing caller facts;
   - single-held-entry frame (including memory-valued StackValue), its
     EVERY lift with each lo unchanged, and raw read_result adaptation;
   - deferred-list forcing composition using that EVERY-preserving unwrap,
     then staging and indexed parameter binding/capacity correspondence.
   The single-entry/EVERY target is written explicitly immediately above;
   the original unframed target is at lines 110-118 and its missing premises
   are explicitly identified by the allocation diagnostic. No diagnostic
   comment in this file is a theorem. Parent forcing is NOT ready to close.
   A semantic implementation PLAN is required before any of these proofs.
*)

(* Current producer coverage audit (C1.6.2.12.16.5).
   The historical unrestricted proposal above is NOT the current interface.
   For nonword LocCode, exprSimCopy.unwrap_runtime_code_copy_sim already
   proves the vv_post-to-expr_post boundary for the actual unwrap operation.
   Its premises, beyond unwrap_value and the location/nonword/runtime split,
   are:
     local_ptrs_reserved cenv sa;
     MAP FDOM es.scopes = MAP FDOM es'.scopes;
     sa.cs_next_var <= sm.cs_next_var;
     sa.cs_next_id <= sm.cs_next_id;
     fn_has_code sm sb func; fn_inst_ids_distinct func;
     !x. p.ptr_operand = Var x ==> not_fresh_at sm x;
     !tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv.
   Reservation is required at sa, not merely at sm. Code membership and
   distinct ids are caller facts about the actual function. Scope domains
   and operand safety must be threaded explicitly: vv_post alone does not
   supply them. expr_sim_inv_memory_size discharges size correspondence
   only given expr_sim_inv at the actual source endpoint. No full source
   state equality is used or implied.

   Exact operation: compile_ensure_in_memory uses compile_alloc_buffer,
   then compile_imm_copy_to_memory F with offset zero. copy_runtime_frag
   handles that compiler (including zero words), not compile_word_copy_loop.
   Its single postcondition contains immutable_transfers memory equality,
   copy_static equality, and all old-variable equalities. copy_runtime_contents
   provides typed contents; the finalised unwrap proof transports allocation,
   operand result and statement relation through copy_buffer_post_transport.
   The resulting expr_post includes stmt_state_rel, expr_val_rel/at, old known
   registers, allocation-map inclusion, separated old-buffer bytes and
   locals_kept. Thus no additional immutable-copy execution induction is
   needed for the unframed LocCode case.

   This does NOT prove the held-entry contract at lines 250ff. expr_post is
   relative to s0 and does not by itself preserve every arbitrary held value
   at the unwrap-entry state. The selected general unframed aggregate output
   is the existing exprSimUnwrap.unwrap_value_sim, not a new wrapper. Besides
   the common premises above, its old-operand premise uses vv_operand vv,
   and its conditional size premise is explicitly:
     !tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
          ~is_word_type (expr_type e) ==>
          type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
          type_memory_size tv < 2 ** 64.
   Apply it directly at the actual source endpoint es'. This audit does not
   discharge that size premise for staging consumers or infer expr_sim_inv
   at es' from scope-domain equality. C1.6.2.12.14 owns
   single-entry and EVERY preservation at the SAME allocation/copy execution
   witness, retaining each lo and advancing its upper boundary sm to sb.
   That proof must retain exact memory/static/old-operand frames, compose
   replay-safe allocation separation, use vv_at_region_frame, and transport
   contents even for memory-valued StackValue. Independently existential
   frag_exec postconditions cannot be conjoined. vv_post_read_result adapts
   the raw input only after this semantic frame is available.
   This comment certifies interface coverage, not either pending theorem.
*)

