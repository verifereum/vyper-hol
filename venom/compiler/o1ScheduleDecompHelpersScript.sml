(*
 * Helpers for o1ScheduleDecomp: lookups in a context with distinct
 * function names, replace_fn, list_index and list_precedes, and what a
 * fn_chain says about its last function.
 *)
Theory o1ScheduleDecompHelpers
Ancestors
  o1FnScheduleDecomp o1PassContract venomFnScheduleRunnerProps
  venomFnScheduleRunner venomInst venomWf fcgDefs list rich_list

Theorem lookup_function_member_iff:
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) ==>
  (lookup_function name fns = SOME fn <=> MEM fn fns /\ fn.fn_name = name)
Proof
  Induct_on `fns` >> simp[lookup_function_def, FIND_thm] >>
  qx_gen_tac `f0` >> rpt strip_tac >> Cases_on `f0.fn_name = name` >> gvs[] >>
  gvs[MEM_MAP, lookup_function_def] >> metis_tac[]
QED

Theorem lookup_function_index_iff:
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) ==>
  (lookup_function name fns = SOME fn <=>
   ?i. i < LENGTH fns /\ EL i fns = fn /\ fn.fn_name = name)
Proof
  strip_tac >> simp[lookup_function_member_iff, MEM_EL] >> metis_tac[]
QED

Theorem replace_fn_length[simp]:
  LENGTH (replace_fn name g fns) = LENGTH fns
Proof
  simp[replace_fn_def]
QED

Theorem replace_fn_names:
  g.fn_name = name ==>
  MAP (\f. f.fn_name) (replace_fn name g fns) = MAP (\f. f.fn_name) fns
Proof
  strip_tac >> simp[replace_fn_def, MAP_COMPOSE, combinTheory.o_DEF, MAP_EQ_f] >>
  rpt strip_tac >> CASE_TAC >> simp[]
QED

Theorem replace_fn_EL:
  i < LENGTH fns ==>
  EL i (replace_fn name g fns) =
    if (EL i fns).fn_name = name then g else EL i fns
Proof
  simp[replace_fn_def, EL_MAP]
QED

Theorem replace_fn_lookup_other:
  g.fn_name = name /\ other <> name ==>
  lookup_function other (replace_fn name g fns) = lookup_function other fns
Proof
  Induct_on `fns` >> simp[replace_fn_def, lookup_function_def, FIND_thm] >>
  qx_gen_tac `f0` >> rpt strip_tac >> Cases_on `f0.fn_name = name` >>
  gvs[replace_fn_def, lookup_function_def]
QED

Theorem ctx_wf_names_entry:
  ctx_fn_names ctx' = ctx_fn_names ctx /\ ctx'.ctx_entry = ctx.ctx_entry ==>
  (ctx_wf ctx' <=> ctx_wf ctx)
Proof
  simp[ctx_wf_def, ctx_distinct_fn_names_def, ctx_has_entry_def]
QED

Theorem o1_ctx_shape_transport:
  o1_ctx_shape ctx /\ ctx_fn_names ctx' = ctx_fn_names ctx /\
  ctx'.ctx_entry = ctx.ctx_entry /\
  EVERY (o1_fn_shape ctx) ctx'.ctx_functions ==>
  o1_ctx_shape ctx'
Proof
  rpt strip_tac >> simp[o1_ctx_shape_def] >> conj_tac
  >- metis_tac[ctx_wf_names_entry, o1_ctx_shape_def]
  >> gvs[EVERY_MEM] >> metis_tac[o1_fn_shape_ctx_eq]
QED

Theorem lookup_unique_function_member_iff:
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) ==>
  (lookup_unique_function name fns = SOME fn <=> MEM fn fns /\ fn.fn_name = name)
Proof
  Induct_on `fns` >> simp[lookup_unique_function_def] >>
  qx_gen_tac `f0` >> rpt strip_tac >> Cases_on `f0.fn_name = name`
  >- (gvs[MEM_MAP] >>
      `FILTER (\f. f.fn_name = f0.fn_name) fns = []` by
        (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
      simp[] >> metis_tac[])
  >> gvs[lookup_unique_function_def] >> metis_tac[]
QED

Theorem list_index_cons:
  list_index x (h::t) =
    if x = h then SOME 0 else OPTION_MAP SUC (list_index x t)
Proof
  simp[list_index_def, INDEX_OF_def, INDEX_FIND_def] >>
  Cases_on `x = h` >> simp[] >>
  qspecl_then [`t`, `1`] (fn th => rewrite_tac[th]) INDEX_FIND_add >>
  Cases_on `INDEX_FIND 0 ($= x) t` >> simp[] >>
  rename1 `INDEX_FIND _ _ _ = SOME p` >> PairCases_on `p` >>
  simp[arithmeticTheory.ADD1]
QED

Theorem list_precedes_cons:
  list_precedes x y (h::t) <=>
  if x = h then y <> h /\ MEM y t
  else y <> h /\ list_precedes x y t
Proof
  simp[list_precedes_def, list_index_cons] >>
  Cases_on `x = h` >> Cases_on `y = h` >> simp[] >>
  Cases_on `list_index x t` >> Cases_on `list_index y t` >>
  gvs[list_index_def, INDEX_OF_eq_NONE] >>
  metis_tac[INDEX_OF_eq_NONE, optionTheory.NOT_SOME_NONE]
QED

Theorem list_precedes_prefix:
  ALL_DISTINCT (done ++ n::todo) ==>
  ~MEM n done /\
  (!x. list_precedes x n (done ++ n::todo) ==> MEM x done) /\
  (!x. MEM x done ==> ~list_precedes n x (done ++ n::todo))
Proof
  Induct_on `done` >> simp[list_precedes_cons] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem distinct_fn_name_index:
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\
  i < LENGTH fns /\ j < LENGTH fns ==>
  ((EL i fns).fn_name = (EL j fns).fn_name <=> i = j)
Proof
  strip_tac >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[EL_MAP]
QED

Theorem fn_chain_last_properties:
  fn_chain rpolicy passes s fs obs /\ EVERY (o1_fn_shape ctx) fs ==>
  (LAST fs).fn_name = (HD fs).fn_name /\ o1_fn_shape ctx (LAST fs)
Proof
  strip_tac >> drule fn_chain_length >> drule fn_chain_names >>
  rpt strip_tac >> `fs <> []` by (strip_tac >> gvs[]) >>
  drule LAST_MEM >> gvs[EVERY_MEM]
QED
