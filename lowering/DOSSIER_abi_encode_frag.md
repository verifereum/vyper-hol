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
| C1.5.1 | proved |  | E0011 | Review and commit; proceed scheduled frontier. C1.5.2 can use enc_prefix_suc, HP_length, enc_prefix_full without unfolding tuple encoding. |

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
