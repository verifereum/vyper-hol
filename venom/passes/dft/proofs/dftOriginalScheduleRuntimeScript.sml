Theory dftOriginalScheduleRuntime
Ancestors
  dftProtectedRuntime dftOccurrenceEditRuntime dftOccurrenceGasEdit dftScheduleEdits venomWf venomInst
  list rich_list sorting relation

Definition dft_original_block_def:
  dft_original_block f b q <=>
    dft_original_schedule f b q /\
    q.bb_instructions <> [] /\
    LAST q.bb_instructions = LAST b.bb_instructions
End

Definition dft_original_function_def:
  dft_original_function f g <=>
    wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
    g = f with fn_blocks := g.fn_blocks /\
    LIST_REL (dft_original_block f) f.fn_blocks g.fn_blocks
End

Definition dft_original_context_def:
  dft_original_context C C' <=>
    C' = C with ctx_functions := C'.ctx_functions /\
    LIST_REL dft_original_function C.ctx_functions C'.ctx_functions
End

Theorem dft_original_block_perm:
  dft_original_block f b q ==> PERM q.bb_instructions b.bb_instructions
Proof
  rw[dft_original_block_def, dft_original_schedule_def] >>
  irule PERM_TRANS >>
  qexists `FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++
    FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions` >>
  conj_tac >- simp[PERM_APPEND_IFF] >>
  metis_tac[PERM_SPLIT, PERM_SYM, combinTheory.o_THM]
QED

Theorem dft_original_block_mem:
  dft_original_block f b q ==>
  (MEM i q.bb_instructions <=> MEM i b.bb_instructions)
Proof
  metis_tac[dft_original_block_perm, PERM_MEM_EQ]
QED

Theorem dft_original_block_output:
  dft_original_block f b q ==>
  ((?i. MEM i q.bb_instructions /\ MEM v i.inst_outputs) <=>
   (?i. MEM i b.bb_instructions /\ MEM v i.inst_outputs))
Proof
  metis_tac[dft_original_block_mem]
QED

Theorem dft_original_block_label:
  dft_original_block f b q ==> q.bb_label = b.bb_label
Proof
  simp[dft_original_block_def, dft_original_schedule_def]
QED

Theorem dft_original_block_succs:
  dft_original_block f b q ==> bb_succs q = bb_succs b
Proof
  strip_tac >> drule dft_original_block_perm >> strip_tac >>
  fs[dft_original_block_def] >>
  `b.bb_instructions <> []` by metis_tac[PERM_NIL] >>
  Cases_on `q.bb_instructions` >> Cases_on `b.bb_instructions` >>
  gvs[bb_succs_def]
QED

Theorem dft_prefix_filter_split[local]:
  !xs. (!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)) ==>
    FILTER P xs ++ FILTER (\x. ~P x) xs = xs
Proof
  Induct >- simp[] >> gen_tac >> disch_tac >>
  `!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
     simp[]) >>
  Cases_on `P h` >- (simp[] >> metis_tac[]) >>
  `FILTER P xs = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_EL] >> rpt strip_tac >>
     qpat_x_assum `!i j. _ /\ _ /\ P (EL j (h::xs)) ==> _`
       (qspecl_then [`0`, `SUC n`] mp_tac) >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

Theorem dft_original_block_refl:
  wf_ssa f /\ wf_function f /\ MEM b f.fn_blocks /\
  EVERY inst_wf b.bb_instructions /\ pseudos_prefix b ==>
  dft_original_block f b b
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++
   FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions = b.bb_instructions` by
    (ho_match_mp_tac dft_prefix_filter_split >> fs[pseudos_prefix_def]) >>
  `b.bb_instructions <> []` by fs[wf_function_def, bb_well_formed_def] >>
  simp[dft_original_block_def, dft_original_schedule_def] >>
  qexists `FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions` >>
  simp[schedule_edges_def]
QED

Theorem dft_original_function_refl:
  wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
  (!b. MEM b f.fn_blocks ==> EVERY inst_wf b.bb_instructions) ==>
  dft_original_function f f
Proof
  strip_tac >> simp[dft_original_function_def] >> irule LIST_REL_refl >>
  rpt strip_tac >> irule dft_original_block_refl >>
  fs[fn_pseudos_prefix_def]
QED

Theorem dft_original_context_refl:
  EVERY (\f. wf_ssa f /\ wf_function f /\ fn_pseudos_prefix f /\
    (!b. MEM b f.fn_blocks ==> EVERY inst_wf b.bb_instructions)) C.ctx_functions ==>
  dft_original_context C C
Proof
  strip_tac >> simp[dft_original_context_def] >> irule LIST_REL_refl >>
  rpt strip_tac >> irule dft_original_function_refl >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_original_blocks_lookup[local]:
  !bs qs. LIST_REL (dft_original_block f) bs qs /\
    lookup_block lbl qs = SOME q ==>
    ?b. lookup_block lbl bs = SOME b /\ dft_original_block f b q
Proof
  Induct >- simp[lookup_block_def, FIND_thm] >> Cases_on `qs` >> simp[] >> rpt strip_tac >>
  `h'.bb_label = h.bb_label` by metis_tac[dft_original_block_label] >>
  fs[lookup_block_def, FIND_thm] >>
  Cases_on `h.bb_label = lbl` >> gvs[] >> metis_tac[]
QED

Theorem dft_original_function_lookup_block:
  dft_original_function f g /\ lookup_block lbl g.fn_blocks = SOME q ==>
  ?b. lookup_block lbl f.fn_blocks = SOME b /\ dft_original_block f b q
Proof
  simp[dft_original_function_def] >> metis_tac[dft_original_blocks_lookup]
QED

Theorem dft_original_function_name:
  dft_original_function f g ==> g.fn_name = f.fn_name
Proof
  strip_tac >> fs[dft_original_function_def] >>
  qpat_x_assum `g = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem dft_original_functions_lookup[local]:
  !fs gs. LIST_REL dft_original_function fs gs /\
    lookup_function nm gs = SOME g ==>
    ?f. lookup_function nm fs = SOME f /\ dft_original_function f g
Proof
  Induct >- simp[lookup_function_def, FIND_thm] >> Cases_on `gs` >> simp[] >> rpt strip_tac >>
  `h'.fn_name = h.fn_name` by metis_tac[dft_original_function_name] >>
  fs[lookup_function_def, FIND_thm] >>
  Cases_on `h.fn_name = nm` >> gvs[] >> metis_tac[]
QED

Theorem dft_original_context_lookup_function:
  dft_original_context C C' /\ lookup_function nm C'.ctx_functions = SOME g ==>
  ?f. lookup_function nm C.ctx_functions = SOME f /\ dft_original_function f g
Proof
  simp[dft_original_context_def] >> metis_tac[dft_original_functions_lookup]
QED

Theorem dft_original_blocks_entry[local]:
  !bs qs. LIST_REL (dft_original_block f) bs qs ==>
    OPTION_MAP (\b. b.bb_label) (if NULL qs then NONE else SOME (HD qs)) =
    OPTION_MAP (\b. b.bb_label) (if NULL bs then NONE else SOME (HD bs))
Proof
  Cases >> Cases >> simp[] >> metis_tac[dft_original_block_label]
QED

Theorem dft_original_function_entry:
  dft_original_function f g ==> fn_entry_label g = fn_entry_label f
Proof
  simp[dft_original_function_def, fn_entry_label_def, entry_block_def] >>
  metis_tac[dft_original_blocks_entry]
QED

Theorem dft_original_blocks_members[local]:
  !bs qs. LIST_REL (dft_original_block f) bs qs ==>
    (!q. MEM q qs ==> ?b. MEM b bs /\ dft_original_block f b q) /\
    (!b. MEM b bs ==> ?q. MEM q qs /\ dft_original_block f b q)
Proof
  Induct >- simp[] >> Cases_on `qs` >> simp[] >> metis_tac[]
QED

Theorem dft_original_function_cfg:
  dft_original_function f g ==> fn_cfg_edge g = fn_cfg_edge f
Proof
  strip_tac >>
  `(!q. MEM q g.fn_blocks ==> ?b. MEM b f.fn_blocks /\ dft_original_block f b q) /\
   (!b. MEM b f.fn_blocks ==> ?q. MEM q g.fn_blocks /\ dft_original_block f b q)` by
    (irule dft_original_blocks_members >> fs[dft_original_function_def]) >>
  simp[FUN_EQ_THM, fn_cfg_edge_def] >> metis_tac[dft_original_block_succs,
    dft_original_block_label]
QED

Theorem dft_original_function_reachable:
  dft_original_function f g ==> (fn_reachable g l <=> fn_reachable f l)
Proof
  strip_tac >> drule dft_original_function_cfg >>
  drule dft_original_function_entry >> simp[fn_reachable_def]
QED

Theorem dft_original_function_path[local]:
  !p. fn_cfg_edge g = fn_cfg_edge f ==> (is_fn_path g p <=> is_fn_path f p)
Proof
  Induct >> simp[is_fn_path_def] >> Cases_on `p` >> simp[is_fn_path_def]
QED

Theorem dft_original_function_dominates:
  dft_original_function f g ==> (fn_dominates g d l <=> fn_dominates f d l)
Proof
  strip_tac >>
  `fn_cfg_edge g = fn_cfg_edge f` by metis_tac[dft_original_function_cfg] >>
  `fn_entry_label g = fn_entry_label f` by metis_tac[dft_original_function_entry] >>
  `!l. fn_reachable g l = fn_reachable f l` by
    metis_tac[dft_original_function_reachable] >>
  `!p. is_fn_path g p = is_fn_path f p` by metis_tac[dft_original_function_path] >>
  simp[fn_dominates_def]
QED

Theorem dft_nonpseudo_swap_prefix[local]:
  !pp pre body. EVERY P pp /\ EVERY (\i. ~P i) body /\
    pp ++ body = pre ++ [x;y] ++ post /\ ~P x /\ ~P y ==>
    ?body'. pre ++ [y;x] ++ post = pp ++ body' /\ PERM body' body
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> gvs[] >>
      simp[PERM_APPEND_IFF, PERM_SWAP_AT_FRONT]) >>
  Cases_on `pre` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists `body'` >> simp[]
QED

Theorem dft_original_block_swap:
  dft_original_block f b q /\ q.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post) ==>
  dft_original_block f b (q with bb_instructions := pre ++ [y;x] ++ post)
Proof
  strip_tac >>
  `is_terminator (LAST q.bb_instructions).inst_opcode` by
    (fs[dft_original_block_def, dft_original_schedule_def, wf_function_def,
        bb_well_formed_def] >> metis_tac[]) >>
  `post <> []` by (Cases_on `post` >> gvs[LAST_APPEND]) >>
  fs[dft_original_block_def, dft_original_schedule_def] >>
  rename1 `PERM code (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions)` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) code` by
    (drule PERM_EVERY >> simp[EVERY_FILTER]) >>
  `?rest. pre ++ [y;x] ++ post =
      FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ rest /\ PERM rest code` by
    (ho_match_mp_tac (Q.INST [{redex = `P`, residue = `\i. is_pseudo i.inst_opcode`}]
       (INST_TYPE [alpha |-> ``:instruction``] dft_nonpseudo_swap_prefix)) >> simp[EVERY_FILTER]) >>
  `LAST (pre ++ [y;x] ++ post) = LAST b.bb_instructions` by
    (Cases_on `post` >- gvs[] >>
     qpat_x_assum `LAST (pre ++ [x;y] ++ _) = _` mp_tac >>
     simp[NoAsms, LAST_APPEND]) >>
  gvs[] >> metis_tac[PERM_TRANS]
QED

Theorem dft_original_block_edit:
  dft_original_block f b q /\ bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  (q = bb0 ==> schedule_edges b.bb_instructions dft_must_order
    (pre ++ [y;x] ++ post)) ==>
  dft_original_block f b (dft_gas_edit_block bb0 pre x y post q)
Proof
  strip_tac >> Cases_on `q = bb0` >> gvs[dft_gas_edit_block_def] >>
  irule dft_original_block_swap >> simp[]
QED

Theorem dft_original_blocks_edit[local]:
  !bs qs. LIST_REL (dft_original_block f) bs qs /\
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  (!b. MEM b bs /\ dft_original_block f b bb0 ==>
    schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post)) ==>
  LIST_REL (dft_original_block f) bs
    (MAP (dft_gas_edit_block bb0 pre x y post) qs)
Proof
  Induct >- simp[] >> Cases_on `qs` >> simp[] >> rpt strip_tac
  >- (irule dft_original_block_edit >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem dft_original_function_edit:
  dft_original_function f g /\ bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  (!b. MEM b f.fn_blocks /\ dft_original_block f b bb0 ==>
    schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post)) ==>
  dft_original_function f (dft_gas_edit_fn bb0 pre x y post g)
Proof
  strip_tac >> fs[dft_original_function_def] >>
  simp[dft_original_function_def, dft_gas_edit_fn_def] >> conj_tac
  >- (qpat_x_assum `g = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  irule dft_original_blocks_edit >> simp[]
QED

Theorem dft_original_functions_edit[local]:
  !fs gs. LIST_REL dft_original_function fs gs /\
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  (!f b. MEM f fs /\ MEM b f.fn_blocks /\ dft_original_block f b bb0 ==>
    schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post)) ==>
  LIST_REL dft_original_function fs (MAP (dft_gas_edit_fn bb0 pre x y post) gs)
Proof
  Induct >- simp[] >> Cases_on `gs` >> simp[] >> rpt strip_tac
  >- (irule dft_original_function_edit >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem dft_original_context_edit:
  dft_original_context C C' /\ bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  (!f b. MEM f C.ctx_functions /\ MEM b f.fn_blocks /\ dft_original_block f b bb0 ==>
    schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post)) ==>
  dft_original_context C (dft_gas_edit_ctx bb0 pre x y post C')
Proof
  strip_tac >> fs[dft_original_context_def] >>
  simp[dft_original_context_def, dft_gas_edit_ctx_def] >> conj_tac
  >- (qpat_x_assum `C' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  irule dft_original_functions_edit >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem dft_original_context_entry:
  dft_original_context C C' ==> C'.ctx_entry = C.ctx_entry
Proof
  strip_tac >> fs[dft_original_context_def] >>
  qpat_x_assum `C' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
