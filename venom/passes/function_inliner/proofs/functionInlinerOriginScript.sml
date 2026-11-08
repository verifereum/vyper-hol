(* Proof-only provenance for intermediate functions.  The input contract is
   used only at the roots: generated functions need not satisfy it again.
   Counter weakening lets functions untouched by another site's rewrite share
   the current global name supply. *)
Theory functionInlinerOrigin
Ancestors
  functionInlinerContract functionInlinerWf functionInlinerDefs cfgTransform
  list

Inductive inliner_fn_origin:
  (!ctx fn.
    inliner_input_ok ctx /\ MEM fn ctx.ctx_functions ==>
    inliner_fn_origin ctx 0 fn) /\
  (!ctx n m fn.
    inliner_fn_origin ctx n fn /\ n <= m ==>
    inliner_fn_origin ctx m fn) /\
  (!ctx n caller callee ist caller' ist'.
    inliner_fn_origin ctx n caller /\
    inliner_fn_origin ctx n callee /\
    ist.is_inline_count = n /\
    inline_one_site caller callee ist = SOME (caller', ist') ==>
    inliner_fn_origin ctx ist'.is_inline_count caller')
End

Theorem inliner_fn_origin_structure:
  !ctx n fn. inliner_fn_origin ctx n fn ==>
    wf_function fn /\
    EVERY (\bb. ~isPREFIX "inl" bb.bb_label \/
      ?k. k < n /\ isPREFIX (inline_prefix k) bb.bb_label) fn.fn_blocks
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[inliner_input_ok_def, listTheory.EVERY_MEM] >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[inline_blocks_bound_mono])
  >> rpt gen_tac >> strip_tac >>
  gvs[Excl "isPREFIX", Excl "isPREFIX_def"] >>
  drule_all inline_one_site_structure >> strip_tac >>
  gvs[Excl "isPREFIX", Excl "isPREFIX_def"]
QED

Theorem inline_call_site_name[simp]:
  (inline_call_site p r caller callee lbl idx).fn_name = caller.fn_name
Proof
  rewrite_tac[inline_call_site_def] >>
  Cases_on `lookup_block lbl caller.fn_blocks` >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem renumber_fn_name[simp]:
  (renumber_fn_inst_ids fn).fn_name = fn.fn_name
Proof
  simp[renumber_fn_inst_ids_def] >> pairarg_tac >> simp[]
QED

Theorem fix_inline_phis_name[simp]:
  (fix_inline_phis l r bb fn).fn_name = fn.fn_name
Proof
  simp[fix_inline_phis_def]
QED

Theorem inline_one_site_name:
  !caller callee ist caller' ist'.
    inline_one_site caller callee ist = SOME (caller',ist') ==>
    caller'.fn_name = caller.fn_name
Proof
  rpt gen_tac >>
  simp[inline_one_site_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  CASE_TAC >> simp[]
QED

Theorem inliner_fn_origin_name:
  !ctx n fn. inliner_fn_origin ctx n fn ==>
    ?root. MEM root ctx.ctx_functions /\ root.fn_name = fn.fn_name
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >> metis_tac[inline_one_site_name]
QED

Theorem inliner_fn_origin_name_not_inline:
  !ctx n fn. inliner_fn_origin ctx n fn ==>
    ~isPREFIX "inl" fn.fn_name
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[inliner_input_ok_def, listTheory.EVERY_MEM] >> metis_tac[])
  >- simp[]
  >> metis_tac[inline_one_site_name]
QED

Theorem inline_call_site_original_label:
  !caller callee n c lbl idx x.
    ~isPREFIX "inl" x /\ ~MEM x (fn_labels caller) ==>
    ~MEM x (fn_labels
      (inline_call_site (inline_prefix n)
        (return_block_label (inline_prefix n) c) caller callee lbl idx))
Proof
  rpt strip_tac >>
  Cases_on `lookup_block lbl caller.fn_blocks`
  >- gvs[inline_call_site_def] >>
  drule inline_call_site_labels >>
  disch_then (qspecl_then [`callee`, `inline_prefix n`,
    `return_block_label (inline_prefix n) c`, `idx`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[MEM_MAP, inline_prefix_def, return_block_label_def,
      stringTheory.STRCAT_ASSOC, stringTheory.isPREFIX_STRCAT] >>
  metis_tac[]
QED

Theorem inline_one_site_original_label:
  !caller callee ist caller' ist' x.
    inline_one_site caller callee ist = SOME (caller',ist') /\
    ~isPREFIX "inl" x /\ ~MEM x (fn_labels caller) ==>
    ~MEM x (fn_labels caller')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_one_site _ _ _ = _` mp_tac >>
  rewrite_tac[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >- simp[] >>
  PairCases_on `x'` >>
  simp[Excl "isPREFIX", Excl "isPREFIX_def"] >> strip_tac >>
  gvs[Excl "isPREFIX", Excl "isPREFIX_def"] >>
  rewrite_tac[renumber_fn_labels] >> CASE_TAC >>
  simp[fix_inline_phis_structure, Excl "isPREFIX", Excl "isPREFIX_def"] >>
  metis_tac[inline_call_site_original_label]
QED

Theorem inliner_fn_origin_input_ok:
  !ctx n fn. inliner_fn_origin ctx n fn ==> inliner_input_ok ctx
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> simp[] >> metis_tac[]
QED

Theorem inliner_fn_origin_separation_aux[local]:
  !ctx n fn. inliner_fn_origin ctx n fn ==>
    inliner_input_ok ctx /\
    !other. MEM other ctx.ctx_functions /\ other.fn_name <> fn.fn_name ==>
      ~MEM other.fn_name (fn_labels fn)
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[inliner_input_ok_def, EVERY_MEM] >> metis_tac[])
  >- metis_tac[]
  >> rpt gen_tac >> strip_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule inline_one_site_name >> strip_tac >>
  `~isPREFIX "inl" other.fn_name` by
    (gvs[inliner_input_ok_def, EVERY_MEM] >> metis_tac[]) >>
  metis_tac[inline_one_site_original_label]
QED

Theorem inliner_fn_origin_separation:
  !ctx n fn. inliner_fn_origin ctx n fn ==>
    !other. MEM other ctx.ctx_functions /\ other.fn_name <> fn.fn_name ==>
      ~MEM other.fn_name (fn_labels fn)
Proof
  metis_tac[inliner_fn_origin_separation_aux]
QED
