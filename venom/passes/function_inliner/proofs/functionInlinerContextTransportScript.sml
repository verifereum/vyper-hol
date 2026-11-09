(* Static context correspondence for one retained-callee site edit. *)
Theory functionInlinerContextTransport
Ancestors
  functionInlinerOrigin functionInlinerSiteLayout fcgAnalysisProps fcgPostorder
  venomInst list

Definition site_replace_def:
  site_replace C f g = C with ctx_functions :=
    MAP (\h. if h.fn_name = f.fn_name then g else h) C.ctx_functions
End

Theorem site_replace_fields[simp]:
  (site_replace C f g).ctx_entry = C.ctx_entry /\
  (site_replace C f g).ctx_global_reserved = C.ctx_global_reserved /\
  MAP (\h. h.fn_name) (site_replace C f g).ctx_functions =
    MAP (\h. if h.fn_name = f.fn_name then g.fn_name else h.fn_name)
      C.ctx_functions
Proof
  simp[site_replace_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> metis_tac[]
QED

Theorem site_replace_lookup_list[local]:
  !fs f g a. lookup_function f.fn_name fs = SOME f /\
    g.fn_name = f.fn_name ==>
    lookup_function a (MAP (\h. if h.fn_name = f.fn_name then g else h) fs) =
      if a = f.fn_name then SOME g else lookup_function a fs
Proof
  rpt strip_tac >>
  `!h. (if h.fn_name = f.fn_name then g else h).fn_name = h.fn_name` by
    (gen_tac >> Cases_on `h.fn_name = f.fn_name` >> simp[]) >>
  simp[lookup_function_map] >> Cases_on `a = f.fn_name`
  >- gvs[] >>
  Cases_on `lookup_function a fs` >> simp[] >>
  drule fmpAnalysisPropsTheory.lookup_function_name >> simp[]
QED

Theorem site_replace_lookup:
  lookup_function f.fn_name C.ctx_functions = SOME f /\
  g.fn_name = f.fn_name ==>
  lookup_function a (site_replace C f g).ctx_functions =
    if a = f.fn_name then SOME g else lookup_function a C.ctx_functions
Proof
  simp[site_replace_def] >> metis_tac[site_replace_lookup_list]
QED

Theorem site_replace_names:
  g.fn_name = f.fn_name ==>
  MAP (\h. h.fn_name) (site_replace C f g).ctx_functions =
    MAP (\h. h.fn_name) C.ctx_functions
Proof
  strip_tac >> simp[] >> irule MAP_CONG >> metis_tac[]
QED

Theorem site_replace_distinct:
  g.fn_name = f.fn_name /\
  ALL_DISTINCT (MAP (\h. h.fn_name) C.ctx_functions) ==>
  ALL_DISTINCT (MAP (\h. h.fn_name) (site_replace C f g).ctx_functions)
Proof
  metis_tac[site_replace_names]
QED

Theorem inliner_call_path_reachable:
  !ctx a b. ctx_wf ctx /\ wf_invoke_targets ctx /\
    inliner_call_path ctx a b /\ fcg_is_reachable (fcg_analyze ctx) a ==>
    fcg_is_reachable (fcg_analyze ctx) b
Proof
  gen_tac >> rewrite_tac[inliner_call_path_def] >>
  `!a b. TC (\x y. MEM y (fcg_get_callees (fcg_analyze ctx) x)) a b ==>
    ctx_wf ctx /\ wf_invoke_targets ctx /\
    fcg_is_reachable (fcg_analyze ctx) a ==>
    fcg_is_reachable (fcg_analyze ctx) b` suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.TC_INDUCT >> conj_tac
  >- (rpt strip_tac >>
      drule_all fcg_analyze_reachable_sound >> strip_tac >>
      drule_all fcg_analyze_callees_sound >> strip_tac >>
      irule fcg_reachable_direct_callee >> metis_tac[]) >>
  metis_tac[]
QED

Theorem qualified_origin_retained_call_rank:
  qualified_origin ctx0 n h /\
  fcg_is_reachable (fcg_analyze ctx0) h.fn_name /\
  MEM inst (fn_insts h) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label a::args /\
  (!caller callee. MEM callee (fcg_get_callees (fcg_analyze ctx0) caller) ==>
    (rank : string -> num) callee < rank caller) ==>
  rank a < rank h.fn_name
Proof
  strip_tac >> drule_all qualified_origin_call_path >>
  metis_tac[inliner_call_path_rank]
QED

Theorem qualified_origin_retained_call_reachable:
  inliner_input_ok ctx0 /\ qualified_origin ctx0 n h /\
  fcg_is_reachable (fcg_analyze ctx0) h.fn_name /\
  MEM inst (fn_insts h) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label a::args ==>
  fcg_is_reachable (fcg_analyze ctx0) a
Proof
  strip_tac >> drule_all qualified_origin_call_path >>
  strip_tac >> irule inliner_call_path_reachable >>
  gvs[functionInlinerContractTheory.inliner_input_ok_def] >> metis_tac[]
QED

Theorem site_replace_retained_callee:
  lookup_function caller.fn_name C.ctx_functions = SOME caller /\
  inline_one_site caller callee ist = SOME (final,ist') /\
  (rank : string -> num) callee.fn_name < rank caller.fn_name ==>
  lookup_function callee.fn_name (site_replace C caller final).ctx_functions =
    lookup_function callee.fn_name C.ctx_functions
Proof
  strip_tac >> drule inline_one_site_name >> strip_tac >>
  drule_all site_replace_lookup >> simp[] >>
  `callee.fn_name <> caller.fn_name` by (strip_tac >> gvs[]) >> simp[]
QED
