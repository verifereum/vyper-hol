# DOSSIER: abi_encode_frag

PLAN: `lowering/PLAN_abi_encode_frag.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0002 |  |
| C1.2 | proved |  | E0005 |  |
| C1.3 | progressed | missing_helper | E0006 | Request C1.3 interface refinement: frame alone cannot preserve Label operands; characterize allowed preservation premise without changing frozen definitions. |
| C1.3.1 | proved |  | E0007 |  |
| C1.3.2 | proved |  | E0008 |  |
| C1.3.3 | proved |  | E0009 |  |
| C1.4 | stuck | risk_mismatch | E0010 | Strategist review: split instruction metadata projection/scratch invariance from memory observations and encoder consumers. Need small generic allocation-state congruence boundary or reusable projection simpset before framed MCOPY/base branches. |
| C1.4.1 | proved |  | E0014 | Review, commit allocation projection boundary, continue instruction framing. |
| C1.4.2 | progressed | other | E0017 | Continue AbiBytestring framed operational consumer and exact ABI-byte integration; C1.4.2 remains open. |
| C1.4.2.1 | proved |  | E0018 | Review and commit fixed-frame instruction boundaries, then begin rounded-length/layout C1.4.2.2. |
| C1.4.2.2 | proved |  | E0020 |  |
| C1.4.2.3 | proved |  | E0024 | Review and commit operational bytestring boundary, then next planned leaf. |
| C1.4.2.4 | proved |  | E0025 | Review, commit typed consumer and layout helpers, then next scheduled leaf. |
| C1.5.1 | proved |  | E0011 | Review and commit; proceed scheduled frontier. C1.5.2 can use enc_prefix_suc, HP_length, enc_prefix_full without unfolding tuple encoding. |
| C1.5.2 | proved |  | E0012 | Review, commit, continue scheduled leaf. |
| C1.5.3 | proved |  | E0013 | Review and commit runtime invariant interface. |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0002`
- blocker: 
- actual effort: 1 sessions, 9 steps, 8 tools, 3 holbuild, 777,170 tok (776,338 in, 832 out, 766,208 cached), 95.7s, $0.1052008

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 3 msgs, 58 steps, 57 tools, 17 holbuild, 3,895,225 tok (3,889,860 in, 5,365 out, 3,803,520 cached), 924.8s, $0.6066820)
  - Plan inversion via generated abi_enc_plan_cases, list induction for sizes/head lengths, static encoding length from memory boundary, enc_tuple_append for cons and dynamic-array layout -> Added checked abi_enc_plans_nil/cons, abi_enc_plans_memory_sizes (map equality, stronger than sum), abi_enc_plan_static, abi_enc_plans_head_lengths (arbitrary accumulator), val_in_memory_static_enc_length, enc_tuple_cons_parts, enc_tuple_nil, enc_dynarray_parts/payload. Existing generated cases supply all constructor inversions. Standard LENGTH_DROP gives payload subtraction identity; static length boundary uses val_in_memory available from enc_pre. (`TO_abi_encode_frag-20261024T233520Z_m0059_t001`)
- `E0002` (proved, , actual effort: 1 sessions, 9 steps, 8 tools, 3 holbuild, 777,170 tok (776,338 in, 832 out, 766,208 cached), 95.7s, $0.1052008)
  - Search exported contractABI theorem names and inspect head_lengths_leq_LENGTH_enc_tuple -> Existing general bound exactly subsumes requested repair: forall ts vs hl tl hds tls n. has_types ts vs ==> head_lengths ts n + SUM (MAP LENGTH hds) <= n + LENGTH (enc_tuple hl tl ts vs hds tls). Set n=0,hds=[],tls=[]; no duplicate added. Removed diagnostic prints and rebuilt. (`TO_abi_encode_frag-20261024T233520Z_m0068_t001`, `TO_abi_encode_frag-20261024T233520Z_m0070_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0068_t001` (use `read_tool_output` for exact output)
- `TO_abi_encode_frag-20261024T233520Z_m0070_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 8 steps, 7 tools, 4 holbuild, 450,283 tok (449,739 in, 544 out, 438,912 cached), 68.6s, $0.0709852

### Attempts / Evidence

- `E0003` (progressed, missing_helper, actual effort: 1 sessions, 3 msgs, 45 steps, 44 tools, 13 holbuild, 4,675,429 tok (4,670,323 in, 5,106 out, 4,607,104 cached), 364.4s, $0.6382084)
  - Prove general subregion, scratch allocation, tuple append/EL, homogeneous EL and pointwise padded memory boundaries -> Target builds. Added enc_pre_bounds, regions_disjoint_subregions, enc_scratch_alloca_bound/outside_disjoint, tuple_in_memory_append/EL, elems_in_memory_EL, mem_bytes_at_pointwise and val_in_memory_pointwise. Last preservation boundary requires val_wf as the library interface does. No new cheats. (`TO_abi_encode_frag-20261024T233520Z_m0122_t001`)
- `E0004` (progressed, other, actual effort: 1 sessions, 3 msgs, 29 steps, 28 tools, 9 holbuild, 3,745,427 tok (3,742,132 in, 3,295 out, 3,561,856 cached), 188.9s, $0.7496876)
  - Implement strategist's mutual value_has_type-to-val_wf induction, typed byte-preservation corollary, then enc_frame source boundary -> Typing bridge and typed pointwise corollary verified through builds. Frame proof at lines 1172-1191 is nearly complete but currently fails at arithmetic leaf: paired lambda has not beta-reduced before decide_tac. Need simplify pair application before arithmetic. No new cheats; main theorem remains untouched. C1.1 stable progress already committed as 53318170; C1.2 remains uncommitted until target builds. (`TO_abi_encode_frag-20261024T233520Z_m0140_t001`, `TO_abi_encode_frag-20261024T233520Z_m0151_t001`)
- `E0005` (proved, , actual effort: 1 sessions, 8 steps, 7 tools, 4 holbuild, 450,283 tok (449,739 in, 544 out, 438,912 cached), 68.6s, $0.0709852)
  - Finish enc_frame_preserves_source with targeted disjointness rewriting, simp[] for paired beta normalization, and arithmetic; retain checked typing and extraction boundaries. -> abiEncoderPropsTheory builds successfully; source preservation and all requested C1.2 boundaries proved without new cheats. (`TO_abi_encode_frag-20261024T233520Z_m0164_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0164_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0006`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 12 steps, 11 tools, 4 holbuild, 808,801 tok (807,581 in, 1,220 out, 789,376 cached), 131.1s, $0.1275476
- next: Request C1.3 interface refinement: frame alone cannot preserve Label operands; characterize allowed preservation premise without changing frozen definitions.

### Attempts / Evidence

- `E0006` (progressed, missing_helper, actual effort: 1 sessions, 1 msgs, 12 steps, 11 tools, 4 holbuild, 808,801 tok (807,581 in, 1,220 out, 789,376 cached), 131.1s, $0.1275476)
  - Prove finite/split/disjoint id intervals and frame reflexivity, then test generic operand preservation from enc_frame. -> Five helpers checked. Generic operand preservation is false for Label because eval_operand reads vs_labels, absent from enc_frame. Removed invalid experimental helper; target builds. Need strategist clarification of preservation interface for labels and reserved scratch credit. (`TO_abi_encode_frag-20261024T233520Z_m0180_t001`, `TO_abi_encode_frag-20261024T233520Z_m0182_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0180_t001` (use `read_tool_output` for exact output)
- `TO_abi_encode_frag-20261024T233520Z_m0182_t001` (use `read_tool_output` for exact output)

## C1.3.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 3 steps, 2 tools, 1 holbuild, 223,902 tok (223,543 in, 359 out, 218,240 cached), 14.7s, $0.0360200

### Attempts / Evidence

- `E0007` (proved, , actual effort: 1 sessions, 3 steps, 2 tools, 1 holbuild, 223,902 tok (223,543 in, 359 out, 218,240 cached), 14.7s, $0.0360200)
  - Case split operands; simplify labels with explicit label equality and transport variable lookups using frame. -> Qualified operand transport theorem builds cleanly. (`TO_abi_encode_frag-20261024T233520Z_m0187_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0187_t001` (use `read_tool_output` for exact output)

## C1.3.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0008`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 25 steps, 24 tools, 11 holbuild, 2,136,338 tok (2,133,224 in, 3,114 out, 2,097,664 cached), 163.1s, $0.3120264

### Attempts / Evidence

- `E0008` (proved, , actual effort: 1 sessions, 2 msgs, 25 steps, 24 tools, 11 holbuild, 2,136,338 tok (2,133,224 in, 3,114 out, 2,097,664 cached), 163.1s, $0.3120264)
  - Partition missing-id sets, prove card addition, restrict scratch with reserved suffix credit, and restore full scratch from unchanged suffix lookups. -> All three required boundaries build cleanly. Proofs use targeted rewrites; removing irrelevant card equalities avoids simplifier timeout in allocation branch. (`TO_abi_encode_frag-20261024T233520Z_m0217_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0217_t001` (use `read_tool_output` for exact output)

## C1.3.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0009`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 2 holbuild, 489,509 tok (488,466 in, 1,043 out, 478,464 cached), 34.7s, $0.0782804

### Attempts / Evidence

- `E0009` (proved, , actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 2 holbuild, 489,509 tok (488,466 in, 1,043 out, 478,464 cached), 34.7s, $0.0782804)
  - Output inclusion weakening and adjacent-fragment frame composition with explicit final global scratch. -> Both boundaries build cleanly. Composition uses second-frame allocation persistence to transfer prefix scratch exclusions to final state. (`TO_abi_encode_frag-20261024T233520Z_m0227_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0227_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch`
- latest episode: `E0010`
- blocker: Instruction/frame component too broad; scratch preservation through memory-only operations needs a projection boundary to avoid timeout from unfolding full state records and alloca invariants.
- actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 7 holbuild, 1,675,176 tok (1,672,303 in, 2,873 out, 1,628,416 cached), 178.7s, $0.2793456
- next: Strategist review: split instruction metadata projection/scratch invariance from memory observations and encoder consumers. Need small generic allocation-state congruence boundary or reusable projection simpset before framed MCOPY/base branches.

### Attempts / Evidence

- `E0010` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 7 holbuild, 1,675,176 tok (1,672,303 in, 2,873 out, 1,628,416 cached), 178.7s, $0.2793456)
  - Prove generic padded write disjoint observation from take_drop_splice_disjoint and zero-extension neutrality; specialize to mcopy. -> Both enc_write_memory_disjoint and enc_mcopy_disjoint proved, retained, target clean. (`TO_abi_encode_frag-20261024T233520Z_m0253_t001`, `TO_abi_encode_frag-20261024T233520Z_m0265_t001`)
  - Frame MCOPY by unfolding enc_frame/enc_scratch and state definitions; then isolate scratch preservation using fs and srw_ss simplification. -> Initial frame goal explodes to record memory implementation; two isolated scratch simplifications time out even with no arithmetic simpset. Removed unproved enc_frame_mcopy experiment. (`TO_abi_encode_frag-20261024T233520Z_m0259_t001`, `TO_abi_encode_frag-20261024T233520Z_m0261_t001`, `TO_abi_encode_frag-20261024T233520Z_m0263_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0265_t001` (use `read_tool_output` for exact output)
- `TO_abi_encode_frag-20261024T233520Z_m0263_t001` (use `read_tool_output` for exact output)

## C1.4.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0014`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 1 holbuild, 602,992 tok (602,005 in, 987 out, 585,344 cached), 49.5s, $0.1017264
- next: Review, commit allocation projection boundary, continue instruction framing.

### Attempts / Evidence

- `E0014` (proved, , actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 1 holbuild, 602,992 tok (602,005 in, 987 out, 585,344 cached), 49.5s, $0.1017264)
  - Prove alloca_inv congruence from allocation map/frontier equality, then enc_scratch congruence without memory unfolding. -> Short simp/forward-chain proofs close on abstract states. ()
  - Prove write_memory and mcopy selector equations, derive scratch preservation with irule enc_scratch_cong. -> All new boundaries build cleanly; consumers never expand memory operations and alloca predicates together. (`TO_abi_encode_frag-20261025T101052Z_m0426_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0426_t001` (use `read_tool_output` for exact output)

## C1.4.2

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0017`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 32 steps, 31 tools, 6 holbuild, 2,122,978 tok (2,119,276 in, 3,702 out, 2,070,400 cached), 227.9s, $0.3418120
- next: Continue AbiBytestring framed operational consumer and exact ABI-byte integration; C1.4.2 remains open.

### Attempts / Evidence

- `E0015` (progressed, other, actual effort: 1 sessions, 2 msgs, 33 steps, 32 tools, 9 holbuild, 2,932,018 tok (2,928,548 in, 3,470 out, 2,886,016 cached), 199.3s, $0.4083656)
  - Prove enc_frame_write_memory and enc_frame_mcopy by simplifying allocation metadata first, then applying disjoint-byte boundaries. -> Both frame proofs build, with metadata and byte reasoning separated. ()
  - Add enc_frame_mstore via existing mstore_eq_wmwe; add instruction-index frame stability; prove compile_abi_encode_copy_frame_frag with exact MCOPY byte effect, labels, result length and frame. -> Clean build. The run_inst_seq lifting adds vs_inst_idx, so byte-effect equality rather than full-state equality is the sound postcondition. Copy length needs mem_size < dimword; this follows from frozen enc_pre source bound at integration. (`TO_abi_encode_frag-20261025T101052Z_m0460_t001`)
- `E0016` (progressed, other, actual effort: 1 sessions, 4 msgs, 63 steps, 62 tools, 17 holbuild, 6,099,928 tok (6,092,553 in, 7,375 out, 6,008,704 cached), 404.7s, $0.8423184)
  - Add scratch/update_var stability, general frame transport through assignments to non-old variables, and MSTORE/update_var commutation. -> Verified boundaries allow primitive postconditions without unfolding memory and allocator predicates together. ()
  - Prove compile_abi_encode_prim_frame_frag using direct two-instruction execution and separate suspended run/post proofs. -> Build clean. Only destination operand must be old; source is consumed before assignment. No fresh_vars_wrt assumption. Exports mem_word_at result, labels, length and full frame. (`TO_abi_encode_frag-20261025T101052Z_m0493_t001`)
- `E0017` (progressed, other, actual effort: 1 sessions, 2 msgs, 32 steps, 31 tools, 6 holbuild, 2,122,978 tok (2,119,276 in, 3,702 out, 2,070,400 cached), 227.9s, $0.3418120)
  - Integrate exact ABI bytes into operational copy and primitive framed consumers using val_in_memory_static_abi and static length boundary. -> compile_abi_encode_copy_abi_frag and compile_abi_encode_prim_abi_frag build clean, exporting exact ABI bytes, size, labels and enc_frame. Primitive helper generalizes to all static 32-byte types. Uses enc_pre_bounds rather than unfolding scratch for word bounds. (`TO_abi_encode_frag-20261025T101052Z_m0529_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0529_t001` (use `read_tool_output` for exact output)

## C1.4.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0018`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 54 steps, 53 tools, 20 holbuild, 5,445,368 tok (5,438,366 in, 7,002 out, 5,370,368 cached), 2243.7s, $0.7430528
- next: Review and commit fixed-frame instruction boundaries, then begin rounded-length/layout C1.4.2.2.

### Attempts / Evidence

- `E0018` (proved, , actual effort: 1 sessions, 4 msgs, 54 steps, 53 tools, 20 holbuild, 5,445,368 tok (5,438,366 in, 7,002 out, 5,370,368 cached), 2243.7s, $0.7430528)
  - Prove fixed-index enc_frame_trans and interval-containing enc_frame_cover_outputs. -> Both boundary lemmas build. Transitivity transports scratch-disjointness backward via preservation of existing allocation entries; cover_outputs handles subinterval writes. (`TO_abi_encode_frag-20261025T101052Z_m0559_t001`)
  - Provide enc_emit_op_run_frame, enc_emit_mcopy_run_frame and enc_emit_mstore_run_frame using existential successors and an independently indexed ambient frame. -> All build without fresh_vars_wrt or nested assignment witnesses; generic op rule preserves operands old at local st. Memory write rules preserve arbitrary operands and require write interval containment in ambient outs. (`TO_abi_encode_frag-20261025T101052Z_m0586_t001`)
  - Compile then remove local ADD/AND/MLOAD consumer probe of enc_emit_op_run_frame. -> All three opcode interfaces checked via raw one-step semantics and generic execution boundary; removed redundant probe from permanent source. Final source build clean. (`TO_abi_encode_frag-20261025T101052Z_m0588_t001`, `TO_abi_encode_frag-20261025T101052Z_m0592_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0588_t001` (use `read_tool_output` for exact output)
- `TO_abi_encode_frag-20261025T101052Z_m0592_t001` (use `read_tool_output` for exact output)

## C1.4.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0020`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 25 steps, 24 tools, 6 holbuild, 1,608,135 tok (1,606,022 in, 2,113 out, 1,567,360 cached), 206.0s, $0.2551900

### Attempts / Evidence

- `E0019` (progressed, other, actual effort: 1 sessions, 3 msgs, 33 steps, 32 tools, 8 holbuild, 4,244,185 tok (4,240,410 in, 3,775 out, 4,101,248 cached), 387.8s, $0.7261988)
  - Prove rounded natural bounds and word-mask agreement through alignmentTheory.align_bitwise_and/align_w2n. -> enc_round32_bounds and enc_round32_word verified. DIVISION needs explicit separate MOD bound retained before simp. (`TO_abi_encode_frag-20261025T101052Z_m0612_t001`)
  - Prove general padded mem_bytes_at subrange boundary via LIST_EQ/EL_TAKE/EL_DROP. -> enc_mem_bytes_subrange verified using explicit index bounds and asm_simp_tac bool_ss to avoid boss simp arithmetic timeout. (`TO_abi_encode_frag-20261025T101052Z_m0626_t001`)
  - Add zero-MSTORE subrange and prezero source-disjointness helpers. -> Unverified tail: build currently stops at static error in enc_mstore_zero_subrange, undeclared TAKE_REPLICATE and MIN_DEF. Must search correct list theorem names/qualified arithmetic theorem. enc_prezero_source follows in source but has not been checked. Full prezero/MCOPY layout remains to write. (`TO_abi_encode_frag-20261025T101052Z_m0628_t001`)
- `E0020` (proved, , actual effort: 1 sessions, 1 msgs, 25 steps, 24 tools, 6 holbuild, 1,608,135 tok (1,606,022 in, 2,113 out, 1,567,360 cached), 206.0s, $0.2551900)
  - Repair zero-store subrange with LIST_EQ/EL_REPLICATE and qualify venomMemDefsTheory.regions_disjoint_def in source preservation. -> Both boundary lemmas build. (`TO_abi_encode_frag-20261025T101052Z_m0645_t001`)
  - Split padded output into copied prefix and zero suffix, apply mcopy_padded_read, enc_mcopy_disjoint and enc_mstore_zero_subrange. -> enc_prezero_copy_layout proved for arbitrary l<=r<=l+32 including zero and empty padding; use LAND_CONV to avoid splitting RHS prefix. (`TO_abi_encode_frag-20261025T101052Z_m0659_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0659_t001` (use `read_tool_output` for exact output)

## C1.4.2.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0024`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 35 steps, 34 tools, 12 holbuild, 2,621,971 tok (2,618,584 in, 3,387 out, 2,555,392 cached), 270.4s, $0.4157932
- next: Review and commit operational bytestring boundary, then next planned leaf.

### Attempts / Evidence

- `E0021` (progressed, other, actual effort: 1 sessions, 2 msgs, 34 steps, 33 tools, 7 holbuild, 3,003,632 tok (2,997,979 in, 5,653 out, 2,952,704 cached), 399.1s, $0.4423504)
  - Specialize existential instruction frame boundary to constant ADD and constant AND using step_ADD/step_AND, not unfolded instruction semantics. -> enc_emit_add_const_run_frame and enc_emit_and_const_run_frame build. ADD handles arbitrary k and l, preserving memory, labels, local-old operands and ambient frame. No bytestring ten-step composition attempted yet. (`TO_abi_encode_frag-20261025T101052Z_m0694_t001`)
- `E0022` (progressed, other, actual effort: 1 sessions, 3 msgs, 46 steps, 45 tools, 11 holbuild, 4,214,172 tok (4,206,831 in, 7,341 out, 4,145,280 cached), 498.9s, $0.6110400)
  - Compose existential constant ADD and AND instruction boundaries into enc_bytes_round_run for the two-instruction rounding sequence. -> Verified run across both emissions, rounded result, memory/labels preservation and ambient frame transitivity. Explicitly specialize residual universal outs after drule_all. emitted_insts_emit_op supplies next-var monotonicity; rev_drule selects first emission rather than AND. (`TO_abi_encode_frag-20261025T101052Z_m0710_t001`)
- `E0023` (progressed, other, actual effort: 1 sessions, 8 msgs, 97 steps, 96 tools, 32 holbuild, 9,319,310 tok (9,301,205 in, 18,105 out, 9,042,944 cached), 1082.0s, $1.6018664)
  - Strengthen rounding interface and prove load/round/pointer prefix, prezero/ADD32/copy writes, and final size suffix as short existential operational runs. -> enc_bytes_load_round_run, enc_bytes_prefix_run, enc_bytes_write_run, enc_bytes_size_run all verified. round_run now exports old-operand preservation, same_blocks and current-insts append. Memory instruction frame coverage antecedents reshaped from existential coverage to explicit out_base/out_len (equivalent universally quantified interface), enabling drule_all against witnesses. (`TO_abi_encode_frag-20261025T101052Z_m0789_t001`)
  - Compose bytestring compiler branch via named compile states and suspended bytes_writes/bytes_lift sections. -> Compiler decomposition, metadata and full prefix run verified. bytes_writes currently fails on w2n src_w bound simp; changed to irule wordsTheory.w2n_lt but not rebuilt before forced handoff. Remaining writes/size composition text is unverified, and bytes_lift contains intentional FAIL_TAC probe. No new cheat added; source currently not build-clean. (`TO_abi_encode_frag-20261025T101052Z_m0805_t001`, `TO_abi_encode_frag-20261025T101052Z_m0813_t001`, `TO_abi_encode_frag-20261025T101052Z_m0814_t001`)
- `E0024` (proved, , actual effort: 1 sessions, 2 msgs, 35 steps, 34 tools, 12 holbuild, 2,621,971 tok (2,618,584 in, 3,387 out, 2,555,392 cached), 270.4s, $0.4157932)
  - Compose prefix/write/size runs with explicitly selected compile-state triples, then lift via frag_exec_run_inst_seq; discharge post with enc_prezero_copy_layout and code safety with projected emit metadata. -> compile_abi_encode_bytes_frame_frag Finalise succeeds; abiEncoderPropsTheory builds. Avoided simplifier timeouts by deleting commutation rewrite facts after use and using pure_asm_rewrite_tac for emitted-list expansion, followed by assumption-free simp_tac for instruction opcode checks. (`TO_abi_encode_frag-20261025T101052Z_m0827_t001`, `TO_abi_encode_frag-20261025T101052Z_m0846_t001`, `TO_abi_encode_frag-20261025T101052Z_m0854_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0854_t001` (use `read_tool_output` for exact output)

## C1.4.2.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0025`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 58 steps, 57 tools, 16 holbuild, 6,590,456 tok (6,584,580 in, 5,876 out, 6,497,152 cached), 593.6s, $0.8833312
- next: Review, commit typed consumer and layout helpers, then next scheduled leaf.

### Attempts / Evidence

- `E0025` (proved, , actual effort: 1 sessions, 4 msgs, 58 steps, 57 tools, 16 holbuild, 6,590,456 tok (6,584,580 in, 5,876 out, 6,497,152 cached), 593.6s, $0.8833312)
  - Prove enc_bytes_memory_layout from padded memory split/word observations, then shared bytes/string typed inversion enc_typed_bytes_layout, and compose operational bytestring consumer under enc_pre. -> compile_abi_encode_bytes_abi_frag covers both BytesT(Dynamic n) and StringT n, includes unchanged labels and arbitrary R. Bounds and disjointness follow from enc_pre and live encoded length. Full abiEncoderPropsTheory build succeeds. (`TO_abi_encode_frag-20261025T101052Z_m0876_t001`, `TO_abi_encode_frag-20261025T101052Z_m0908_t001`, `TO_abi_encode_frag-20261025T101052Z_m0917_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0917_t001` (use `read_tool_output` for exact output)

## C1.5.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0011`
- blocker: 
- actual effort: 1 sessions, 5 msgs, 78 steps, 77 tools, 26 holbuild, 8,230,469 tok (8,222,119 in, 8,350 out, 8,124,672 cached), 618.4s, $1.0908612
- next: Review and commit; proceed scheduled frontier. C1.5.2 can use enc_prefix_suc, HP_length, enc_prefix_full without unfolding tuple encoding.

### Attempts / Evidence

- `E0011` (proved, , actual effort: 1 sessions, 5 msgs, 78 steps, 77 tools, 26 holbuild, 8,230,469 tok (8,222,119 in, 8,350 out, 8,124,672 cached), 618.4s, $1.0908612)
  - Define recursive separated heads/tails and HP/TP/DP; prove zero and paired append, then successor via TAKE_EL_SNOC. -> All prefix equations checked; successor uses fixed boundary and cumulative tail length, not prefix head size. (`TO_abi_encode_frag-20261024T233520Z_m0293_t001`)
  - Prove typed head length using enc_has_static_length and RHS-only head_lengths_add; derive typed tuple assembly using cons-parts and head-length slice simplification. -> enc_prefix_head_length, enc_prefix_assembly, HP_length and enc_prefix_full proved. Assembly appropriately requires has_types as authorized. (`TO_abi_encode_frag-20261024T233520Z_m0320_t001`, `TO_abi_encode_frag-20261024T233520Z_m0355_t001`)
  - Prove static tails vanish and dynamic homogeneous heads have length 32*k. -> enc_prefix_tail_static, TP_static, HP_dynamic_length proved. Required explicit TAKE/GENLIST arithmetic and removal of redundant TAKE equality before final simplification to avoid rewrite interaction. (`TO_abi_encode_frag-20261024T233520Z_m0355_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0355_t001` (use `read_tool_output` for exact output)

## C1.5.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0012`
- blocker: 
- actual effort: 1 sessions, 11 steps, 10 tools, 4 holbuild, 1,452,290 tok (1,450,206 in, 2,084 out, 1,433,344 cached), 77.7s, $0.1978984
- next: Review, commit, continue scheduled leaf.

### Attempts / Evidence

- `E0012` (proved, , actual effort: 1 sessions, 11 steps, 10 tools, 4 holbuild, 1,452,290 tok (1,450,206 in, 2,084 out, 1,433,344 cached), 77.7s, $0.1978984)
  - Define enc_prefix_mem and prove zero, successor from four final-state byte slices, separated exit assembly and contiguous exit when B=head_lengths. -> All required memory-prefix interfaces proved. Use pure rewrites for LENGTH_APPEND and padded split before arithmetic simplification, preserving head-before-tail order; otherwise simp commutes sum operands and splits the wrong slice first. (`TO_abi_encode_frag-20261024T233520Z_m0371_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261024T233520Z_m0371_t001` (use `read_tool_output` for exact output)

## C1.5.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0013`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 6 holbuild, 1,881,821 tok (1,879,226 in, 2,595 out, 1,834,112 cached), 229.9s, $0.2995892
- next: Review and commit runtime invariant interface.

### Attempts / Evidence

- `E0013` (proved, , actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 6 holbuild, 1,881,821 tok (1,879,226 in, 2,595 out, 1,834,112 cached), 229.9s, $0.2995892)
  - Define enc_array_inv with predicate inv_ctx and optional tail_cell; prove zero, successor packaging and separate elimination facts by simplification. -> All packaging facts build; renamed K and cp to avoid existing HOL constant clashes. ()
  - Prove memory-prefix, operand and frame jump stability, then enc_array_header jump stability and condition extraction. -> Build clean. Header uses explicit stable-context premise and never assumes frame transport from a child. (`TO_abi_encode_frag-20261025T101052Z_m0413_t001`)

### Evidence refs

- `TO_abi_encode_frag-20261025T101052Z_m0413_t001` (use `read_tool_output` for exact output)
