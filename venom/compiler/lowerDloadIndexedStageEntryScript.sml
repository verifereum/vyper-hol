Theory lowerDloadIndexedStageEntry
Ancestors
  lowerDloadStageEntry
  o1PassContract venomInst list

(* Indexed lookup boundary: retains the original relation witness, rather
   than projecting it to a fresh existential supply. *)
Theorem ld_lookup_function_indexed:
  !fs gs name g.
    LIST_REL R fs gs /\
    (!f h. R f h ==> h.fn_name = f.fn_name) /\
    lookup_function name gs = SOME g ==>
    ?f pre post before after.
      fs = pre ++ f::post /\ gs = before ++ g::after /\
      LENGTH pre = LENGTH before /\
      lookup_function name fs = SOME f /\ R f g
Proof
  Induct >> namedCases_on `gs` ["", "dst rest"] >>
  simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  `dst.fn_name = h.fn_name` by metis_tac[] >>
  Cases_on `dst.fn_name = name` >> gvs[]
  >- (qexistsl_tac [`[]`, `fs`, `[]`, `rest`] >> simp[]) >>
  `lookup_function name rest = SOME g` by simp[lookup_function_def] >>
  qpat_x_assum `!gs name g. _` drule_all >> strip_tac >>
  qexistsl_tac [`f`, `h::pre`, `post`, `dst::before`, `after`] >>
  gvs[lookup_function_def] >> metis_tac[]
QED

Theorem lower_dload_stage_lookup_indexed:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C'.ctx_functions = SOME g ==>
  ?f pre post before after observed a out.
    C.ctx_functions = pre ++ f::post /\
    C'.ctx_functions = before ++ g::after /\
    LENGTH pre = LENGTH before /\
    lookup_function name C.ctx_functions = SOME f /\
    fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed a f out /\
    out.fpo_function = g /\
    observed.cu_context.ctx_entry = C.ctx_entry /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    view C' f observed
Proof
  simp[ctx_pass_stage_def] >> rpt strip_tac >>
  drule ld_lookup_function_indexed >>
  disch_then (qspecl_then [`name`, `g`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> gvs[fn_pass_step_def])) >>
  strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
