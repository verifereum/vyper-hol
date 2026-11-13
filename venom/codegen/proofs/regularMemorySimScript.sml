Theory regularMemorySim
Ancestors
  codegenRel asmSem strongPrefixSim spillSim contextCodegenRelProps list
  rich_list arithmetic

(* A padded byte range does not require equal physical memory lengths. *)
Theorem memory_rel_padded_range:
  memory_rel alloc vm am /\
  (len = 0 \/ off + len <= alloc.sa_spill_base \/
   alloc.sa_next_offset <= off) ==>
  GENLIST (\i. read_byte (off + i) vm) len =
  GENLIST (\i. read_byte (off + i) am) len
Proof
  strip_tac >> irule GENLIST_CONG >> simp[] >>
  rpt strip_tac >> fs[memory_rel_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem expanded_slice_padded_range:
  off + len <= k ==>
  TAKE len (DROP off (asm_expand_memory k mem)) =
  GENLIST (\i. read_byte (off + i) mem) len
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `DROP off expanded` >>
  `k <= LENGTH expanded` by simp[Abbr `expanded`] >>
  `off + len <= LENGTH expanded` by decide_tac >>
  `LENGTH (TAKE len (DROP off expanded)) = len` by
    (simp[LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
  irule LIST_EQ >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      simp[EL_TAKE, EL_DROP, EL_GENLIST] >>
      `off + x < LENGTH expanded` by decide_tac >>
      `EL (off + x) expanded = read_byte (off + x) expanded` by
        simp[read_byte_def] >>
      simp[Abbr `expanded`, read_byte_expand]) >>
  simp[]
QED

Theorem memory_rel_expanded_slice:
  memory_rel alloc vm am /\
  (len = 0 \/ off + len <= alloc.sa_spill_base \/
   alloc.sa_next_offset <= off) ==>
  TAKE len (DROP off (asm_expand_memory (off + len) vm)) =
  TAKE len (DROP off (asm_expand_memory (off + len) am))
Proof
  simp_tac pure_ss [expanded_slice_padded_range, LESS_EQ_REFL] >>
  strip_tac >> irule memory_rel_padded_range >>
  qexists_tac `alloc` >> asm_rewrite_tac[]
QED

(* Disjointness at the final, larger spill interval implies disjointness
   at the earlier allocation used by the emit step. *)
Theorem spill_range_disjoint_mono:
  earlier.sa_spill_base = later.sa_spill_base /\
  earlier.sa_next_offset <= later.sa_next_offset /\
  (len = 0 \/ off + len <= later.sa_spill_base \/
   later.sa_next_offset <= off) ==>
  (len = 0 \/ off + len <= earlier.sa_spill_base \/
   earlier.sa_next_offset <= off)
Proof
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem inst_memory_safe_mono:
  earlier.sa_spill_base = later.sa_spill_base /\
  earlier.sa_next_offset <= later.sa_next_offset /\
  inst_memory_safe later inst vs vs' ==>
  inst_memory_safe earlier inst vs vs'
Proof
  rw[inst_memory_safe_def, step_mem_safe_def,
     source_memory_writes_disjoint_def, EVERY_MEM] >>
  first_x_assum drule >> PairCases_on `e` >> simp[] >> decide_tac
QED

Theorem word_of_bytes_padded_range:
  word_of_bytes be a (GENLIST (\i. read_byte (off + i) mem) len) =
  word_of_bytes be a (TAKE len (DROP off mem))
Proof
  `GENLIST (\i. read_byte (off + i) mem) len =
   TAKE len (DROP off (asm_expand_memory (off + len) mem))` by
    (sym_tac >> irule expanded_slice_padded_range >> simp[]) >>
  asm_rewrite_tac[word_of_bytes_take_drop_expand]
QED

Theorem spill_window_byte_frame:
  (!i. off <= i /\ i < off + 32 ==>
       read_byte i am' = read_byte i am) ==>
  word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off am')) =
  word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off am))
Proof
  strip_tac >>
  rewrite_tac[GSYM word_of_bytes_padded_range] >>
  AP_TERM_TAC >> irule GENLIST_CONG >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* A writer supplies byte framing outside its declared destination.  Bounds
   on occupied slots then lift that footprint to the spill relation. *)
Theorem plan_spill_rel_matched_write_frame:
  plan_spill_rel lo vs spilled am /\
  (!op. op IN FDOM spilled ==>
        operand_val vs' lo op = operand_val vs lo op) /\
  (!op slot. FLOOKUP spilled op = SOME slot ==>
     alloc.sa_spill_base <= slot /\ slot + 32 <= alloc.sa_next_offset) /\
  (len = 0 \/ off + len <= alloc.sa_spill_base \/
   alloc.sa_next_offset <= off) /\
  (!i. ~(off <= i /\ i < off + len) ==>
       read_byte i am' = read_byte i am) ==>
  plan_spill_rel lo vs' spilled am'
Proof
  strip_tac >> irule plan_spill_rel_preserved >>
  qexists_tac `am` >> qexists_tac `vs` >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule spill_window_byte_frame >> rpt strip_tac >>
  first_x_assum irule >>
  qpat_x_assum `!op slot. FLOOKUP spilled op = SOME slot ==> _`
    drule >> strip_tac >> decide_tac
QED

(* The single MAX expansion used by MCOPY is safe even for overlapping
   source/destination ranges: the copied bytes come from the pre-write view. *)
Theorem memory_rel_mcopy_source_slice:
  memory_rel alloc vm am /\
  (len = 0 \/ src + len <= alloc.sa_spill_base \/
   alloc.sa_next_offset <= src) ==>
  TAKE len (DROP src (asm_expand_memory
    (MAX (src + len) (dst + len)) vm)) =
  TAKE len (DROP src (asm_expand_memory
    (MAX (src + len) (dst + len)) am))
Proof
  `src + len <= MAX (src + len) (dst + len)` by
    (simp[MAX_DEF] >> decide_tac) >>
  asm_simp_tac pure_ss [expanded_slice_padded_range] >>
  strip_tac >> irule memory_rel_padded_range >>
  qexists_tac `alloc` >> asm_rewrite_tac[]
QED

Theorem read_byte_overwrite:
  off + LENGTH bytes <= LENGTH mem ==>
  read_byte i (TAKE off mem ++ bytes ++ DROP (off + LENGTH bytes) mem) =
  if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
  else read_byte i mem
Proof
  strip_tac >>
  `off <= LENGTH mem` by decide_tac >>
  simp[read_byte_def, LENGTH_TAKE, LENGTH_DROP] >>
  Cases_on `i < off` >> simp[]
  >- simp[EL_APPEND1, EL_TAKE] >>
  Cases_on `i < off + LENGTH bytes` >> simp[]
  >- simp[EL_APPEND2, EL_APPEND1] >>
  Cases_on `i < LENGTH mem` >> simp[EL_APPEND2, EL_DROP] >>
  AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem memory_rel_overwrite:
  memory_rel alloc vm am /\
  off + LENGTH bytes <= LENGTH vm /\
  off + LENGTH bytes <= LENGTH am ==>
  memory_rel alloc
    (TAKE off vm ++ bytes ++ DROP (off + LENGTH bytes) vm)
    (TAKE off am ++ bytes ++ DROP (off + LENGTH bytes) am)
Proof
  rw[memory_rel_def] >>
  asm_simp_tac bool_ss [read_byte_overwrite] >>
  Cases_on `off <= i /\ i < off + LENGTH bytes` >> simp[]
QED

Theorem short_return_write_frame:
  off + capacity <= LENGTH mem /\
  ~(off <= i /\ i < off + capacity) ==>
  read_byte i
    (TAKE off mem ++ TAKE capacity data ++
     DROP (off + LENGTH (TAKE capacity data)) mem) =
  read_byte i mem
Proof
  strip_tac >>
  `LENGTH (TAKE capacity data) <= capacity` by simp[LENGTH_TAKE_EQ] >>
  `off + LENGTH (TAKE capacity data) <= LENGTH mem` by decide_tac >>
  asm_simp_tac bool_ss [read_byte_overwrite] >>
  `~(off <= i /\ i < off + LENGTH (TAKE capacity data))` by decide_tac >>
  simp[]
QED
