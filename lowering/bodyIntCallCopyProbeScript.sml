(* Semantic probe for deferred aggregate forcing: one copied slot, not
   aggregate layout correctness. *)
Theory bodyIntCallCopyProbe
Ancestors
  exprSimStorageCopy valueEncodingProps exprLoweringProps venomExecSemantics
  venomState venomInst emitHelperProps

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

   The unrestricted runtime boundary must have exactly the parameters and
   conclusion of unwrap_runtime_noncopy_sim, dropping its case restriction
   and retaining ~cenv.ce_is_ctor.  Equivalently its hypotheses are:
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
   theorem assumes compile_expr, not unwrap_value, so it cannot supply
   the required frame by instantiation.  vv_post_read_result handles raw
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
