(* Resource invariance for the proof-only return marker. *)
Theory entryReturnMarkerResources
Ancestors
  entryReturnMarker allocaHistory exprLoweringProps ptrDiscipline fcgDefs
  venomWf venomInst list rich_list finite_map

Theorem return_marker_fields[simp]:
  (return_marker_inst id).inst_id = id /\
  (return_marker_inst id).inst_opcode = GAS /\
  (return_marker_fn f label idx id).fn_name = f.fn_name
Proof
  simp[return_marker_inst_def, mk_inst_def, return_marker_fn_def]
QED

Theorem marker_inst_split[local]:
  !bbs. fn_insts_blocks (return_marker_blocks label idx id bbs) =
        fn_insts_blocks bbs \/
        ?xs ys. fn_insts_blocks bbs = xs ++ ys /\
          fn_insts_blocks (return_marker_blocks label idx id bbs) =
            xs ++ return_marker_inst id :: ys
Proof
  Induct >> simp[return_marker_blocks_def, fn_insts_blocks_def] >>
  gen_tac >> IF_CASES_TAC >> simp[fn_insts_blocks_def]
  >- (disj2_tac >>
      qexistsl [`TAKE idx h.bb_instructions`,
                `DROP idx h.bb_instructions ++ fn_insts_blocks bbs`] >>
      simp[GSYM APPEND_ASSOC]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- simp[] >>
  disj2_tac >> qexistsl [`h.bb_instructions ++ xs`, `ys`] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[]
QED

Theorem return_marker_insts_split:
  !f label idx id. fn_insts (return_marker_fn f label idx id) = fn_insts f \/
  ?xs ys. fn_insts f = xs ++ ys /\
          fn_insts (return_marker_fn f label idx id) =
            xs ++ return_marker_inst id :: ys
Proof
  rpt gen_tac >> mp_tac (Q.SPEC `f.fn_blocks` marker_inst_split) >>
  simp[fn_insts_def, return_marker_fn_def]
QED

Theorem return_marker_inst_mem:
  i.inst_opcode <> GAS ==>
  (MEM i (fn_insts (return_marker_fn f label idx id)) <=> MEM i (fn_insts f))
Proof
  strip_tac >>
  qspecl_then [`f`,`label`,`idx`,`id`] strip_assume_tac return_marker_insts_split >>
  gvs[MEM_APPEND] >>
  `i <> return_marker_inst id` by (strip_tac >> gvs[]) >> simp[]
QED

Theorem return_marker_insts_include:
  MEM i (fn_insts f) ==> MEM i (fn_insts (return_marker_fn f label idx id))
Proof
  qspecl_then [`f`,`label`,`idx`,`id`] strip_assume_tac return_marker_insts_split >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem return_marker_filter[local]:
  ~P (return_marker_inst id) ==>
  FILTER P (fn_insts (return_marker_fn f label idx id)) = FILTER P (fn_insts f)
Proof
  strip_tac >>
  qspecl_then [`f`,`label`,`idx`,`id`] strip_assume_tac return_marker_insts_split >>
  simp[FILTER_APPEND]
QED

Theorem marker_id_flatten[local]:
  !bbs. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs) =
        MAP (\i. i.inst_id) (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND]
QED

Theorem return_marker_distinct:
  fn_inst_ids_distinct f /\ (!i. MEM i (fn_insts f) ==> i.inst_id <> id) ==>
  fn_inst_ids_distinct (return_marker_fn f label idx id)
Proof
  qspecl_then [`f`,`label`,`idx`,`id`] strip_assume_tac return_marker_insts_split >>
  simp[fn_inst_ids_distinct_def, marker_id_flatten, GSYM fn_insts_def] >>
  gvs[MEM_APPEND, ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem return_marker_lookup_function:
  lookup_function name (return_marker_ctx ctx f label idx id).ctx_functions =
  OPTION_MAP (\g. if g = f then return_marker_fn g label idx id else g)
    (lookup_function name ctx.ctx_functions)
Proof
  simp[return_marker_ctx_def] >> irule lookup_function_map >> rw[]
QED

Theorem return_marker_function_mem:
  MEM f ctx.ctx_functions ==>
  MEM (return_marker_fn f label idx id)
    (return_marker_ctx ctx f label idx id).ctx_functions
Proof
  simp[return_marker_ctx_def, MEM_MAP] >> metis_tac[]
QED

Theorem return_marker_calls[local]:
  fn_directly_calls (return_marker_ctx ctx f label idx id) = fn_directly_calls ctx
Proof
  simp[FUN_EQ_THM, fn_directly_calls_def, return_marker_lookup_function] >>
  rpt gen_tac >> Cases_on `lookup_function x ctx.ctx_functions` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `INVOKE <> GAS` by simp[] >> metis_tac[return_marker_inst_mem]
QED

Theorem return_marker_pending[local]:
  pending_alloca_size (return_marker_fn f label idx id) s =
  pending_alloca_size f s
Proof
  simp[pending_alloca_size_def] >> AP_TERM_TAC >> AP_TERM_TAC >>
  irule return_marker_filter >> simp[]
QED

Theorem marker_unit_filter[local]:
  !fns. FILTER (\i. i.inst_opcode = ALLOCA)
    (FLAT (MAP fn_insts
      (MAP (\g. if g = f then return_marker_fn f label idx id else g) fns))) =
  FILTER (\i. i.inst_opcode = ALLOCA) (FLAT (MAP fn_insts fns))
Proof
  Induct >> simp[FILTER_APPEND] >> gen_tac >> IF_CASES_TAC >>
  simp[return_marker_filter]
QED

Theorem return_marker_unit[local]:
  unit_alloca_frame (return_marker_ctx ctx f label idx id) = unit_alloca_frame ctx
Proof
  simp[unit_alloca_frame_def, return_marker_ctx_def, marker_unit_filter]
QED

Theorem return_marker_dalloca_fn[local]:
  EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts (return_marker_fn f label idx id)) =
  EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)
Proof
  simp[EXISTS_MEM] >>
  `DALLOCA <> GAS` by simp[] >> metis_tac[return_marker_inst_mem]
QED

Theorem marker_dalloca_list[local]:
  !fns. EXISTS (\g. EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts g))
    (MAP (\g. if g = f then return_marker_fn f label idx id else g) fns) =
  EXISTS (\g. EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts g)) fns
Proof
  Induct >> simp[] >> gen_tac >> IF_CASES_TAC >> simp[return_marker_dalloca_fn]
QED

Theorem return_marker_ctx_dalloca[local]:
  ctx_has_dalloca (return_marker_ctx ctx f label idx id) = ctx_has_dalloca ctx
Proof
  simp[ctx_has_dalloca_def, return_marker_ctx_def, marker_dalloca_list]
QED

Theorem return_marker_resources:
  pending_alloca_size (return_marker_fn f label idx id) s = pending_alloca_size f s /\
  unit_alloca_frame (return_marker_ctx ctx f label idx id) = unit_alloca_frame ctx /\
  fn_directly_calls (return_marker_ctx ctx f label idx id) = fn_directly_calls ctx /\
  ctx_has_dalloca (return_marker_ctx ctx f label idx id) = ctx_has_dalloca ctx /\
  EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts (return_marker_fn f label idx id)) =
    EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f) /\
  (alloca_room ctx f s ==>
   alloca_room (return_marker_ctx ctx f label idx id) (return_marker_fn f label idx id) s) /\
  (lookup_function f.fn_name ctx.ctx_functions = SOME f ==>
   alloca_room (return_marker_ctx ctx f label idx id) (return_marker_fn f label idx id) s ==>
   alloca_room ctx f s) /\
  (fmp_room (return_marker_ctx ctx f label idx id) (return_marker_fn f label idx id) s <=>
   fmp_room ctx f s)
Proof
  simp[return_marker_pending, return_marker_unit, return_marker_calls,
       return_marker_dalloca_fn,
       return_marker_ctx_dalloca, alloca_room_def, fmp_room_def,
       return_marker_lookup_function] >> metis_tac[]
QED

Theorem marker_fetch_splice[local]:
  bb.bb_instructions = xs ++ ys ==>
  get_instruction
    (bb with bb_instructions := xs ++ return_marker_inst id :: ys) k =
  if k < LENGTH xs then get_instruction bb k
  else if k = LENGTH xs then SOME (return_marker_inst id)
  else get_instruction bb (k - 1)
Proof
  strip_tac >> Cases_on `k < LENGTH xs`
  >- (`k < LENGTH xs + LENGTH ys /\ k < LENGTH xs + SUC (LENGTH ys)` by decide_tac >>
      simp[get_instruction_def, EL_APPEND_EQN]) >>
  Cases_on `k = LENGTH xs`
  >- (`k < LENGTH xs + SUC (LENGTH ys)` by decide_tac >>
      simp[get_instruction_def, EL_APPEND_EQN]) >>
  `k - LENGTH xs = SUC (k - 1 - LENGTH xs) /\ ~(k - 1 < LENGTH xs)` by decide_tac >>
  `(k < LENGTH xs + SUC (LENGTH ys)) = (k - 1 < LENGTH xs + LENGTH ys)` by decide_tac >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem marker_block_order[local]:
  bb.bb_instructions = xs ++ ys ==>
  (alloca_block_order
     (bb with bb_instructions := xs ++ return_marker_inst id :: ys) sites <=>
   alloca_block_order bb sites)
Proof
  strip_tac >> iff_tac
  >- (strip_tac >> rw[alloca_block_order_def] >>
      qabbrev_tac `i' = if i < LENGTH xs then i else SUC i` >>
      qabbrev_tac `j' = if j < LENGTH xs then j else SUC j` >>
      `i' < j'` by (unabbrev_all_tac >> rw[] >> decide_tac) >>
      `get_instruction
         (bb with bb_instructions := xs ++ return_marker_inst id :: ys) i' = SOME earlier` by
        (simp[marker_fetch_splice, Abbr `i'`] >> rw[] >> gvs[] >> decide_tac) >>
      `get_instruction
         (bb with bb_instructions := xs ++ return_marker_inst id :: ys) j' = SOME later` by
        (simp[marker_fetch_splice, Abbr `j'`] >> rw[] >> gvs[] >> decide_tac) >>
      fs[alloca_block_order_def] >> metis_tac[]) >>
  strip_tac >> rw[alloca_block_order_def] >>
  qabbrev_tac `i' = if i < LENGTH xs then i else i - 1` >>
  qabbrev_tac `j' = if j < LENGTH xs then j else j - 1` >>
  `i <> LENGTH xs /\ j <> LENGTH xs` by
    (conj_tac >> strip_tac >> gvs[marker_fetch_splice]) >>
  `i' < j'` by (unabbrev_all_tac >> rw[] >> decide_tac) >>
  `get_instruction bb i' = SOME earlier` by
    (unabbrev_all_tac >> gvs[marker_fetch_splice] >> rw[] >> gvs[]) >>
  `get_instruction bb j' = SOME later` by
    (unabbrev_all_tac >> gvs[marker_fetch_splice] >> rw[] >> gvs[]) >>
  fs[alloca_block_order_def] >> metis_tac[]
QED

Theorem marker_orders[local]:
  !bbs. EVERY (\bb. alloca_block_order bb sites)
    (return_marker_blocks label idx id bbs) <=>
  EVERY (\bb. alloca_block_order bb sites) bbs
Proof
  Induct >> simp[return_marker_blocks_def] >> gen_tac >> IF_CASES_TAC >>
  simp[marker_block_order]
QED

Theorem marker_cursor_history[local]:
  (s.vs_current_bb = label ==> s.vs_inst_idx <= idx) ==>
  ((!bb k inst.
      lookup_block s.vs_current_bb (return_marker_fn f label idx id).fn_blocks = SOME bb /\
      k < s.vs_inst_idx /\ get_instruction bb k = SOME inst /\
      inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP s.vs_allocas inst.inst_id)) <=>
   (!bb k inst. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
      k < s.vs_inst_idx /\ get_instruction bb k = SOME inst /\
      inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP s.vs_allocas inst.inst_id)))
Proof
  simp[return_marker_lookup] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >> simp[] >>
  Cases_on `s.vs_current_bb = label` >> gvs[] >>
  rename1 `lookup_block label f.fn_blocks = SOME bb` >>
  `!k inst. k < s.vs_inst_idx /\ inst.inst_opcode = ALLOCA ==>
     (get_instruction (bb with bb_instructions :=
       TAKE idx bb.bb_instructions ++ return_marker_inst id :: DROP idx bb.bb_instructions) k =
       SOME inst <=> get_instruction bb k = SOME inst)` suffices_by metis_tac[] >>
  rpt gen_tac >> strip_tac >> Cases_on `idx <= LENGTH bb.bb_instructions`
  >- (`k < idx` by decide_tac >> simp[marker_fetch_splice, LENGTH_TAKE_EQ]) >>
  Cases_on `k < LENGTH bb.bb_instructions`
  >- simp[marker_fetch_splice, LENGTH_TAKE_EQ] >>
  Cases_on `k = LENGTH bb.bb_instructions`
  >- (`inst <> return_marker_inst id` by (strip_tac >> gvs[]) >>
      simp[marker_fetch_splice, LENGTH_TAKE_EQ, get_instruction_def]) >>
  `~(k - 1 < LENGTH bb.bb_instructions)` by decide_tac >>
  simp[marker_fetch_splice, LENGTH_TAKE_EQ, get_instruction_def]
QED

Theorem return_marker_history:
  (s.vs_current_bb = label ==> s.vs_inst_idx <= idx) ==>
  (alloca_history (return_marker_fn f label idx id) s <=> alloca_history f s)
Proof
  strip_tac >> simp[alloca_history_def, marker_cursor_history] >>
  simp[return_marker_fn_def, GSYM EVERY_MEM, marker_orders]
QED
