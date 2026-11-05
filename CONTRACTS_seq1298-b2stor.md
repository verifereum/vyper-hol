# C1.1.b review artifact (E0005 evidence repair)

All contracts below are PROPOSED, not proved/admitted. No theorem statement or definition has changed. Build `placeStoreStorageTheory` passed, evidence TO_seq1298-b2stor-20261105T061837Z_m0131_t001 (cached clean build). Existing main cheat remains. This diagnostic does not lower parent risk.

## D1 child dead implies root dead

```sml
!root path delta leaf base st j b.
 storage_subregion root path delta leaf /\
 dead_bytes st (base + delta) leaf j b ==>
 dead_bytes st base root j b
```

Consumer C1.3 needs the contrapositive, root live implies child live, NOT root dead implies child dead. Induct on storage_subregion/path, generalizing base/st/j/b. Fixed arrays select the same index. Dynamic ancestors: if selected index below length recurse; otherwise all bytes of that element are dead. The inactive case needs dead_bytes boundedness (dead implies within its type's region and b<32), by mutual type/list/fields induction. Tuple/struct use prefix offsets. No reachability below current dynamic length may be assumed: provenance is capacity based. D1's subregion premise comes directly from storage_place_region after place_ptr_rel rules out other places.

## D2 outside-child root dead-byte frame

```sml
!root path delta leaf base st st' j b.
 storage_subregion root path delta leaf /\ 0 < type_slot_size leaf /\
 (!q. ~(base+delta <= w2n q /\ w2n q < base+delta+type_slot_size leaf) ==>
       lookup_storage q st' = lookup_storage q st) /\
 ~(base+delta <= j /\ j < base+delta+type_slot_size leaf) /\
 base + type_slot_size root <= dimword (:256) /\
 dead_bytes st base root j b ==>
 dead_bytes st' base root j b
```

Consumer C1.3 outside-leaf storage_agree. Path induction generalizing both storages/base/j/b. A child write cannot change ancestor dynamic length words or siblings' length words. Positive leaf size and subregion bounds avoid zero-sized-child corner cases. Tuple/struct prefix decomposition as D1; dynamic inactive elements retain ancestor length. This is NOT supplied by nested_pop_dead_bytes_subregion: that existing theorem is local, and covers decrementing a dynamic array header only.

At the frozen call site: positive leaf size is an explicit premise at evaluated dty; root bound from storage_layout_safe in expr_sim_inv; lookup frame from write_storage_slot's encoding support. Other declared roots disjoint from the containing root use the simpler disjoint frame. D2 plus storage_dead_def yields global old-dead => new-dead outside the leaf. Root bounds/disjointness must be instantiated from actual provenance; they are not new target hypotheses.

## D3 shorter-copy arbitrary subregion agreement

```sml
!cx tr mid name subs rootk root path delta leaf k v writes st1 st2 n ws.
 declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
 storage_subregion root path delta leaf /\ w2n k = w2n rootk + delta /\
 w2n rootk + type_slot_size root <= dimword (:256) /\
 (!mid' name' subs' k' tv'.
   declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
   (k',tv') <> (rootk,root) ==>
   ranges_disjoint (w2n rootk) (type_slot_size root) (w2n k') (type_slot_size tv')) /\
 well_formed_type_value leaf /\ value_has_type leaf v /\
 0 < type_slot_size leaf /\ encode_value leaf v = SOME writes /\
 n <= type_slot_size leaf /\
 (!i b. i < type_slot_size leaf /\ b < 32 /\
   ~dead_bytes (apply_writes k writes st1) (w2n k) leaf (w2n k+i) b ==>
   i < n /\
   EL b (word_to_bytes (lookup_storage (k+n2w i) (apply_writes k writes st1)) T) =
   EL b (word_to_bytes (ws i) T)) /\
 storage_agree (storage_dead cx tr st1) st1 st2 ==>
 storage_agree (storage_dead cx tr (apply_writes k writes st1))
   (apply_writes k writes st1)
   (FOLDL (\t i. update_storage (k+n2w i) (ws i) t) st2 (COUNT_LIST n))
```

Consumer C1.3. This exposes only representation-independent live-byte obligation: D4 must discharge it. Inside leaf, D1 and safe declared root show child-dead implies globally dead; live-byte premise gives copy hit. Outside leaf both encoding and copy unchanged, and D2/global-dead frame preserve original agreement. No-wrap from storage_subregion_bounds. Root witness from storage_place_region, NOT a declaration at leaf. Capacity/disjointness from storage_layout_safe (expr_sim_inv conjunct). Leaf type/encoding from place_ptr_rel, widening and successful write_place. Initial agreement from stmt_state_rel. Copy size bounds and byte equality remain real D4 obligations, not consequences of provenance alone.

Existing admitted `storage_agree_copy_region` is inadequate: its signature is

```sml
!cx tr mid n subs k tv v writes off mem ws st1 st2.
 declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
 w2n k + type_slot_size tv <= dimword (:256) /\
 (!mid' n' subs' k' tv'.
   declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
   (k',tv') <> (k,tv) ==>
   ranges_disjoint (w2n k) (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
 well_formed_type_value tv /\ value_has_type tv v /\
 val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
 (!i. i < type_slot_size tv /\
   (?b. b < 32 /\ ~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n k+i) b) ==>
   ws i = mem_word_at (off+32*i) mem) /\
 storage_agree (storage_dead cx tr st1) st1 st2 ==>
 storage_agree (storage_dead cx tr (apply_writes k writes st1))
   (apply_writes k writes st1)
   (FOLDL (\t i. update_storage (k+n2w i) (ws i) t) st2
     (COUNT_LIST (type_slot_size tv)))
```

Read evidence TO_seq1298-b2stor-20261105T061837Z_m0138_t001 lines488-508. It needs declared leaf and full capacity; leave it untouched.

## D4 equal layout / widened bytestring source live bytes

```sml
!tenv dty sty dtv stv v off mem k writes st i b.
 type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
 evaluate_type tenv dty = SOME dtv /\
 (dty = sty \/ (is_bytestring_type dty /\ is_bytestring_type sty)) /\
 well_formed_type_value dtv /\ value_has_type stv v /\ value_has_type dtv v /\
 val_in_memory stv v off mem /\ encode_value dtv v = SOME writes /\
 w2n k + type_slot_size dtv <= dimword (:256) /\
 i < type_slot_size dtv /\ b < 32 /\
 ~dead_bytes (apply_writes k writes st) (w2n k) dtv (w2n k+i) b ==>
 i < type_memory_size stv DIV 32 /\
 EL b (word_to_bytes (lookup_storage (k+n2w i) (apply_writes k writes st)) T) =
 EL b (word_to_bytes (mem_word_at (off+32*i) mem) T)
```

Consumer D3, ws memory words, n source memory size DIV32 for bytestring, destination memory size DIV32 for equal layout. Equal layout uses admitted `encode_value_memory_live` plus slot/memory size alignment. Full signature:

```sml
!tv v off mem k writes st j b.
 well_formed_type_value tv /\ value_has_type tv v /\
 val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
 w2n k + type_slot_size tv <= dimword (:256) /\
 j < type_slot_size tv /\ b < 32 /\
 ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b ==>
 EL b (word_to_bytes
   (lookup_storage (n2w (w2n k+j)) (apply_writes k writes st)) T) =
 EL b (word_to_bytes (mem_word_at (off+32*j) mem) T)
```

Source m0138 lines420-430. Bytes branch genuinely missing: split bytes/string constructors, length first, then bytes below v's length, partial word padding. Widening bounds length by source capacity; capacity bounds n. Frozen expr_val_rel gives source val_in_memory; evaluated type and widening give destination typing/wellformedness; successful write gives encoding. Existing metadata size interfaces identify compiler sizes with semantic sizes. For normalized non-bytes layout, use encode_value_memory_live at dtv with full capacity, not D4.

Nested example: root Fixed[2] Bytes[64] base0, selected leaf base3, source Bytes[1], n=2. New slot3 length=1, slot4 byte0 live; slot4 remaining bytes dead; slot5 entirely dead, hence untouched old tail irrelevant. D1 lifts to root. Checked `place_store_bytes_child_probe` in target source proves this instance; it is not a proof of D1/D4. No tail zero hypothesis.

## N1 counted typed normalization

```sml
!cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
 compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\ EVERY (\(fname,fty,sz). !tv.
     evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
 type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
 evaluate_type tenv dty = SOME dtv /\ value_has_type stv v /\ value_has_type dtv v /\
 val_wf stv v /\ val_wf dtv v /\
 (!x. src = Var x ==> not_fresh_at sa x) /\
 (!x. dst = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
 val_in_memory stv v (w2n sw) s.vs_memory /\
 w2n sw + type_memory_size stv < dimword (:256) /\
 w2n dw + type_memory_size dtv < dimword (:256) /\
 (w2n sw + type_memory_size stv <= w2n dw \/
  w2n dw + type_memory_size dtv <= w2n sw) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
 ?t. gas_marked_path F ctx func s 0 (OK t) /\
 val_in_memory dtv v (w2n dw) t.vs_memory /\
 typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
 ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
 t.vs_inst_idx = LENGTH sb.cs_current_insts
```

Consumer C1.4 at post-allocation state. Existing compile_store_memory_typed_run has these premises except distinct IDs and supplies representation, endpoints, same-record frame, variable frame, memory interval frame, memory length monotonicity, and ONLY this execution conclusion:

```sml
!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
 ?fuel'. run_from fuel' ctx func s = r
```

Full existing signature source lowering/typedMemoryCopyScript.sml lines3531-3568, evidence TO_seq1298-b2stor-20261105T061837Z_m0141_t001. It does NOT imply N1's gas path. typed_copy_state_frame definition:

```sml
typed_copy_state_frame sa off len s t <=>
 (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
           vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
           vs_inst_idx := s.vs_inst_idx|>) = s /\
 (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
 typed_copy_frame off len s.vs_memory t.vs_memory
```

Thus allocas, alloca_next, storage, call_ctx, halted unchanged. N1 is missing, not admitted elsewhere. Rank/type-widening induction matching typed_copy_rank_entry, generalized over operands, compile states, function/context, machine state and pointers. Need stronger internal child-entry interface carrying paths instead of frag_exec. Base words MLOAD/MSTORE, bytes MCOPY; tuples/structs offset setup + child composition; fixed arrays unrolling or loop; dynamic arrays header + bounded element loop. Nested dynamic arrays are NOT excluded by frozen top-level condition. Each loop needs branch/jump gas edges and state frame; existing continuation proof is not logically convertible. No new definition yet proposed; strategist may justify a path-entry predicate.

N1 call-site discharge: metadata consistency/field sizes from expr_sim_inv; source/destination type/value/val_wf via widening/preservation interfaces; source memory rep from expr_val_rel. Source strict bound from frozen nonword bound plus machine allocation invariant; destination bound/disjointness from new buffer allocation + local_ptrs_reserved. Source variable freshness from frozen premise + monotonicity; buffer operand not_fresh_at at LATER typed-copy start. Code and endpoint premises by splitting compilation and fn_has_code. These numeric/allocation facts require actual instantiation against allocator output before main-proof authorization: no extra hypotheses may be added to target. Prior allocation inventory is evidence only; a complete call-site derivation is not claimed here. Unresolved cases are recursive collection/dynamic-array counted paths and their frames. Separate counted memory-to-storage/transient loop contract still needed for C1.5: N1 is normalization only.

## Review request / limits

D1-D4/N1 are specifications, not compiled/proved helpers. Main target unchanged. No source implementation authorized until strategist reviews. General dead-byte and recursive counted-copy obligations remain high risk. Ancestor admissions may be used freely; existing local lemmas are not exported. Proposed scopes: semantic boundedness/path-frame helpers; shorter-copy live-byte helper; recursive counted normalization; counted storage suffix; then frozen main composition. This list is a proposal to strategist, not an executor-created PLAN.

## C1.1.i source audit (current, partial diagnostic)

D1/D2/global frame and abstract D3 are now checked target helpers; abstract agreement committed 655a5cabc (E0014). No concrete D3/D4 or N1 proof is claimed here.

### D3 support verified
- `semantics/prop/vyperEncodeDecodeScript.sml:1008` exported `encode_writes_bounded`, conjunct 1: encode_value tv v = SOME writes and value_has_type tv v imply every offset in MAP FST writes is < type_slot_size tv.
- At :1314 exported `apply_writes_lookup_miss_num`: if every written `n2w(base+off)` differs from `n2w(base+k)`, lookup at that address after apply_writes(n2w base) is unchanged. Its observation address is base+k, so it does not directly match addresses below base; modular offset or a more general finite-update boundary is needed there.
- `storageCopyLiveScript.sml:436-480` fold hit/frame and encoded-outside helpers are LOCAL, not reusable exports. `copyExecution.slot_copy_lookup` is a CODE block lookup, not a storage fold lookup.
- Minimal suggested genuinely more general interface for strategist review: lookup of an arbitrary finite list of storage updates (not restricted COUNT_LIST) in terms of the last matching write, with a miss clause. Both apply_writes and FOLDL COUNT_LIST can instantiate it; this should avoid duplicating local copy_fold_region/copy_encoded_outside statements. Requires strategist authorization before implementation.
- Abstract place_store_subregion_agree consumes st1'=apply_writes k writes st1 and st2'=counted fold. Its source frame follows bounded encoding plus no-wrap; target frame/hit follow finite-update lookup plus injectivity within n<=leaf size. D4 supplies i<n and the new-byte equality. No declaration at leaf needed.

### D4 important simplification
`valueEncodingScript.sml:166-180` shows val_in_memory for dynamic BytesV and StringV is CAPACITY INDEPENDENT: header word n2w(length bs), and mem_bytes_at(off+32)(length bs)=bs. Thus source val_in_memory stv implies val_in_memory dtv by constructor equations when both are widened bytes or both strings. The already admitted exported `encode_value_memory_live` (:420-430) can then supply ALL required byte equalities at destination layout. A separate payload encoding proof is unnecessary. Remaining novel D4 output is only the shorter-copy live-index bound i < source capacity words+1.
`vyperStorageScript.sml:126-130,199-203`: encoding is length header followed by MAPi(i+1) bytes_to_slots; only checks length<=capacity. `compileEnvScript.sml:1009-1019`: payload byte dead iff base<j<=base+word_size destination capacity, b<32, and encoded header length<=32*(j-(base+1))+b. Header i=0 always within source copy; for i>0 liveness implies 32*(i-1)+b<length<=source capacity. This implies i<1+word_size source capacity; all later words are dead, including padding in last word. Need checked header lookup fact; existing copy_dyn_head/apply_writes_lookup_0 are local, so request a general encode/decode header interface rather than duplicate local statements.
`compile_assign_value_def:405` chooses type_memory_bytes source for bytestring destination, otherwise supplied destination mem_size; :446-453 and :472-479 choose one MLOAD/store for <=32, otherwise DIV32 words. Bytestring capacity0 => n=1 and single-load branch, not zero copies. Semantic type_slot_size for bytes/string is 1+word_size capacity (`vyperValueScript.sml:32-34`); compiler memory bytes is 32+((capacity+31) DIV32)*32 (`compileEnvScript.sml:1782-1783`). Equal-layout and normalized cases use full destination size with encode_value_memory_live.

### N1 checked execution boundary and allocation premises
`contextScript.sml:671-696` dispatches word MLOAD/MSTORE; bytes compile_store_bytestring; invalid only for cyclic metadata (excluded); dynamic and fixed array helpers; tuple per-field recursion; struct per-field recursion; fallback flat copy. :704-714 fields compose byte-offset setup, child copy and rest. :719-747 fixed arrays either flat copy (equal elem sizes and not ABI-dynamic) or a counter loop with LT/ISZERO/JNZ, MUL/ADD element pointers, recursive child, increment/JMP. :751-780 dynamic arrays load/assert capacity/store header, compute data pointers, then dynamic flat copy for equal elements or analogous child loop. Nested dynamic arrays remain reachable.
`typedMemoryCopyScript.sml:3415-3528` rank induction already isolates these cases, but its typed_copy_entry consumers all return frag_exec; :3531-3568 compile_store_memory_typed_run has continuation execution only. Cannot convert to counted path.
Counted building blocks verified: fragGasPath gas_path_edge_normal, gas_path_normal, gas_path_then; fragGasMode gas_marked_path_then and from_mem. These are generic edges/composition, NOT typed-loop correctness. Need new counted word/bytes flat-copy boundaries, child-path loop invariants for arrays (including dynamic length), and sequential field/struct path composition, with typed_copy_state_frame retained. No existing typed gas path was found in typedMemoryCopyScript.
`exprSimAllocScript.sml:69-90` literal_alloc_buffer_run is the closest frozen-call-site allocator: premises compile allocation, stmt_state_rel, distinct IDs, local_ptrs_reserved, size<dimword, and instruction membership; outputs run_inst_seq, stmt_state_rel, evaluated buffer, FLOOKUP new allocation=(w2n w,size), strict end bound, memory unchanged, next-id increase, old vars/allocations preserved, and buf operand Var p not_fresh_at later state. buffer_alloc_code (:123-128) supplies membership from fn_has_code. This is not itself a gas path.
Postallocation disjointness follows frozen nonword source separation for allocation ids>=sa.next_id: if allocator reused entry, apply original separation to that entry; otherwise fresh buffer base must be >=old alloca_next and frozen source end<=old alloca_next. literal_alloc_buffer_run does NOT explicitly expose the latter fresh-base property; literal_alloca_run proof or an exported allocator site theorem must be checked. Strict source end bound still needs stmt_state_rel allocation bound + source end<=alloca_next, not merely non-strict frozen source bound. Destination strict bound supplied directly by literal_alloc_buffer_run. New buffer freshness supplied at sm; old op freshness needs cs_extends monotonicity. Metadata/type/value/val_wf discharge from expr_sim_inv and widening remains to be checked by exact lemma signatures. These unverified call-site items prevent main-proof authorization.

Evidence: TO_seq1298-b2stor-20261105T080825Z_m0380_t001, m0381_t001, m0386_t001, m0388_t001, m0389_t001, m0402_t001, m0404_t001, m0406_t001, m0408_t001, m0412_t001, m0416_t001 (same tool-output prefix). This report is intentionally partial pending remaining call-site signature audit.

### C1.1.i final call-site signature checks
- `vyperTypeArgFits.type_widens_to_value_has_type` (:104-107) takes exactly widening, source evaluation and source typing and returns destination evaluation plus typing. `valueEncodingTyping.value_has_type_val_wf` (:14-19), conjunct1, gives val_wf from typing alone. `vyperTypeValues.evaluate_type_well_formed_type_value` is the evaluated-type wellformedness boundary (signature still needs instantiation at context tenv). No extra val_wf target premise is needed.
- `expr_sim_inv_def:44-49` has exactly N1 sfields_tenv_consistent plus field distinctness/semantic sizes. :52 has storage_layout_safe. Hence these do not require a new invariant.
- `exprLoweringProps.alloca_room_next_lt:469-470`: alloca_room ctx func ss ==> ss.vs_alloca_next < dimword. With stmt_state_rel's alloca_room and frozen source end<=next this gives source strict bound. Allocation does not change memory; old variables survive.
- `venomExecSemantics.exec_alloca_def:573-588` supplies the missing fresh-base computation: NONE allocation returns n2w old vs_alloca_next; SOME(offset,sz) returns n2w offset. Together with literal_alloc_buffer_run's strict end and new FLOOKUP this should prove either old entry at allocator id or new base=old next. That shape is NOT exported by literal_alloc_buffer_run. A boundary strengthening in a NEW theorem (not editing existing ancestor theorem) is required; it should include counted ALLOCA path and this reuse/fresh dichotomy, so source separation can be discharged without implementation unfolding at the main consumer. Existing allocator owned-run is continuation-only.
- State/endpoints after run_inst_seq require actual execution-path composition; do not identify literal_alloc_buffer_run's t with a gas-path endpoint without proving that bridge.

Diagnostic deliverable complete as an inventory of verified and explicitly missing interfaces, not proof of D3/D4/N1. Suggested strategist scope: finite-update observation interface; bytes live-index bound using capacity-independent val_in_memory; postallocation counted boundary with reuse/fresh dichotomy; counted recursive typed entry with separate loop/field composition. Generic gas edge interfaces alone do not derisk these recursive outputs.
