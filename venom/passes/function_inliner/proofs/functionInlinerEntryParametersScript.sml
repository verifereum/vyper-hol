(* Distinguished entry prefixes survive edits modulo instruction identifiers. *)
Theory functionInlinerEntryParameters
Ancestors
  functionInlinerOccurrences functionInlinerSiteLayout callLayoutDefs
  functionInlinerEnvelopes functionInlinerOrigin functionInlinerWf
  cfgTransformProps venomExecProps venomInst functionInlinerDefs list rich_list

Theorem inline_param_fields_cong:
  inline_inst_fields a = inline_inst_fields b ==>
  (param_inst_at k a <=> param_inst_at k b)
Proof
  simp[inline_inst_fields_def, param_inst_at_def] >> metis_tac[]
QED

Theorem inline_param_prefix_fields_cong:
  !xs ys k. MAP inline_inst_fields xs = MAP inline_inst_fields ys ==>
  (param_insts_from k xs <=> param_insts_from k ys)
Proof
  Induct >> Cases_on `ys` >> simp[param_insts_from_def] >>
  rpt strip_tac >> metis_tac[inline_param_fields_cong]
QED

Theorem inline_parameter_prefix_no_invoke:
  !params k j. param_insts_from k params /\ j < LENGTH params ==>
  (EL j params).inst_opcode <> INVOKE /\ (EL j params).inst_opcode <> PHI
Proof
  rpt strip_tac >> drule_all param_insts_from_el >>
  simp[param_inst_at_def, is_param_opcode_def] >> metis_tac[]
QED

Theorem inline_call_site_parameter_prefix:
  lookup_block l caller.fn_blocks = SOME eb /\
  eb.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  lookup_block lbl caller.fn_blocks = SOME cb /\
  i < LENGTH cb.bb_instructions /\ (EL i cb.bb_instructions).inst_opcode = INVOKE ==>
  ?eb' tail'. lookup_block l (inline_call_site p r caller callee lbl i).fn_blocks = SOME eb' /\
    eb'.bb_label = eb.bb_label /\ eb'.bb_instructions = params ++ tail'
Proof
  strip_tac >> Cases_on `l = lbl`
  >- (gvs[] >>
      `LENGTH params <= i` by
        (Cases_on `i < LENGTH params` >> simp[] >>
         drule_all inline_parameter_prefix_no_invoke >> gvs[EL_APPEND_EQN]) >>
      drule inline_call_site_lookup_call >>
      disch_then (qspecl_then [`r`, `p`, `i`, `callee`] mp_tac) >> strip_tac >>
      simp[] >> qexists `DROP (LENGTH params) (TAKE i (params ++ tail)) ++
        [<|inst_id := 0; inst_opcode := JMP;
           inst_operands := [Label (case (clone_function p callee).fn_blocks of
             [] => "" | eb::_ => eb.bb_label)]; inst_outputs := []|>]` >>
      simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, APPEND_ASSOC, DROP_APPEND2] >>
      metis_tac[lookup_block_label]) >>
  drule_all inline_call_site_lookup_other >>
  disch_then (qspecl_then [`r`, `p`, `i`, `callee`] mp_tac) >>
  metis_tac[]
QED

Theorem inline_fix_phis_parameter_prefix:
  lookup_block l fn.fn_blocks = SOME eb /\
  eb.bb_instructions = params ++ tail /\ param_insts_from 0 params ==>
  ?eb' tail'. lookup_block l (fix_inline_phis old fresh ret fn).fn_blocks = SOME eb' /\
    eb'.bb_label = eb.bb_label /\ eb'.bb_instructions = params ++ tail'
Proof
  strip_tac >>
  `MAP (\inst. if inst.inst_opcode <> PHI then inst
     else subst_label_inst old fresh inst) params = params` by
    (rewrite_tac[LIST_EQ_REWRITE] >> simp[EL_MAP] >> rpt strip_tac >>
     drule_all inline_parameter_prefix_no_invoke >> simp[]) >>
  drule functionInlinerPhiTransportTheory.inline_fix_phis_lookup_some >>
  disch_then (qspecl_then [`ret`, `old`, `fresh`] mp_tac) >>
  Cases_on `MEM eb.bb_label (bb_succs ret)` >> simp[MAP_APPEND] >>
  metis_tac[]
QED

Theorem inline_renumber_parameter_prefix:
  lookup_block l fn.fn_blocks = SOME eb /\
  eb.bb_instructions = params ++ tail /\ param_insts_from 0 params ==>
  ?eb' params' tail'.
    lookup_block l (renumber_fn_inst_ids fn).fn_blocks = SOME eb' /\
    eb'.bb_label = eb.bb_label /\ eb'.bb_instructions = params' ++ tail' /\
    LENGTH params' = LENGTH params /\
    MAP inline_inst_fields params' = MAP inline_inst_fields params /\
    param_insts_from 0 params'
Proof
  strip_tac >> drule inline_renumber_lookup_some >> strip_tac >>
  qexistsl [`bb'`, `TAKE (LENGTH params) bb'.bb_instructions`,
    `DROP (LENGTH params) bb'.bb_instructions`] >> simp[TAKE_DROP] >>
  `LENGTH bb'.bb_instructions = LENGTH params + LENGTH tail` by
    metis_tac[LENGTH_MAP, LENGTH_APPEND] >>
  `MAP inline_inst_fields (TAKE (LENGTH params) bb'.bb_instructions) =
    MAP inline_inst_fields params` by
    (rewrite_tac[MAP_TAKE] >> simp[TAKE_APPEND]) >>
  simp[] >> metis_tac[inline_param_prefix_fields_cong]
QED

Theorem inline_one_site_parameter_prefix:
  ALL_DISTINCT (fn_labels caller) /\
  lookup_block l caller.fn_blocks = SOME eb /\
  eb.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  inline_one_site caller callee ist = SOME (result,ist') ==>
  ?eb' params' tail'. lookup_block l result.fn_blocks = SOME eb' /\
    eb'.bb_label = eb.bb_label /\ eb'.bb_instructions = params' ++ tail' /\
    LENGTH params' = LENGTH params /\
    MAP inline_inst_fields params' = MAP inline_inst_fields params /\
    param_insts_from 0 params'
Proof
  strip_tac >>
  qpat_x_assum `inline_one_site _ _ _ = _` mp_tac >>
  rewrite_tac[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >> simp[] >>
  PairCases_on `x` >> simp[] >> strip_tac >>
  drule_all find_invoke_site_lookup >> strip_tac >>
  drule_all inline_call_site_parameter_prefix >>
  disch_then (qspecl_then
    [`return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter`,
     `inline_prefix ist.is_inline_count`, `callee`] strip_assume_tac) >>
  Cases_on `lookup_block
    (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
    (inline_call_site (inline_prefix ist.is_inline_count)
      (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
      caller callee x0 x1).fn_blocks` >> gvs[] >>
  metis_tac[inline_fix_phis_parameter_prefix, inline_renumber_parameter_prefix]
QED

Theorem inline_annotated_entry_parameter_prefix:
  !ctx n root cert. inline_annotated_origin ctx n root cert ==>
  !entry rest params tail.
    (inline_entry_function cert).fn_blocks = entry::rest /\
    entry.bb_instructions = params ++ tail /\ param_insts_from 0 params ==>
    ?eb ps post. lookup_block entry.bb_label root.fn_blocks = SOME eb /\
      eb.bb_label = entry.bb_label /\ eb.bb_instructions = ps ++ post /\
      LENGTH ps = LENGTH params /\
      MAP inline_inst_fields ps = MAP inline_inst_fields params /\
      param_insts_from 0 ps
Proof
  ho_match_mp_tac inline_annotated_origin_strongind >> rpt conj_tac >>
  simp[inline_entry_function_def]
  >- (rpt strip_tac >>
      `lookup_block entry.bb_label root.fn_blocks = SOME entry` by
        simp[lookup_block_def, FIND_thm] >> metis_tac[]) 
  >> map_every qx_gen_tac [`ctx`, `caller`, `callee`, `ist`, `result`, `ist'`, `a`, `b`] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `wf_function caller` by
    metis_tac[inline_annotated_origin_erasure, qualified_origin_erasure,
      inliner_fn_origin_structure] >>
  `ALL_DISTINCT (fn_labels caller)` by gvs[venomWfTheory.wf_function_def] >>
  qpat_x_assum `!entry rest params tail. (inline_entry_function a).fn_blocks = _ /\ _ ==> _`
    (qspecl_then [`entry`, `rest`, `params`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inline_one_site_parameter_prefix >> strip_tac >>
  metis_tac[]
QED

Theorem inline_parameter_prefix_fetch:
  eb.bb_instructions = ps ++ post /\
  MAP inline_inst_fields ps = MAP inline_inst_fields params /\
  param_insts_from 0 ps /\ j < LENGTH params ==>
  MAP inline_inst_fields (TAKE j eb.bb_instructions) =
    MAP inline_inst_fields (TAKE j params) /\
  OPTION_MAP inline_inst_fields (get_instruction eb j) =
    SOME (inline_inst_fields (EL j params)) /\
  param_inst_at j (EL j ps)
Proof
  strip_tac >>
  `LENGTH ps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  `j < LENGTH ps` by simp[] >>
  `inline_inst_fields (EL j ps) = inline_inst_fields (EL j params)` by
    metis_tac[EL_MAP] >>
  simp[TAKE_APPEND, MAP_TAKE, get_instruction_def, EL_APPEND_EQN] >>
  metis_tac[param_insts_from_el, arithmeticTheory.ADD_CLAUSES]
QED

Theorem inline_annotated_entry_parameter_address:
  inline_annotated_origin ctx n root cert /\
  (inline_entry_function cert).fn_blocks = entry::rest ==>
  inline_namespace_leaf_at cert (inline_entry_address cert) I
    (inline_entry_function cert) /\
  root.fn_blocks <> [] /\ (HD root.fn_blocks).bb_label = entry.bb_label
Proof
  strip_tac >> simp[inline_entry_leaf] >>
  drule inline_annotated_entry_first_label >> simp[]
QED
