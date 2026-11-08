(* Proof-only provenance for intermediate functions.  The input contract is
   used only at the roots: generated functions need not satisfy it again.
   Counter weakening lets functions untouched by another site's rewrite share
   the current global name supply. *)
Theory functionInlinerOrigin
Ancestors
  functionInlinerContract functionInlinerWf functionInlinerDefs cfgTransform
  indexedLists venomInst venomWfProps list fcgAnalysisProps fmpLowerProps

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

(* Rewriting introduces only assignments and continuation jumps. Other
   surviving instructions are unchanged, in particular nested calls. *)
Theorem rewrite_inline_inst_survivor:
  !args outs ret inst pi ri.
    MEM ri (FST (rewrite_inline_inst args outs ret inst pi)) /\
    ri.inst_opcode <> ASSIGN /\ ri.inst_opcode <> JMP ==>
    ri = inst
Proof
  rpt gen_tac >>
  simp[rewrite_inline_inst_def, AllCaseEqs(), SF boolSimps.COND_elim_ss, MEM_MAPi] >>
  rpt strip_tac >> gvs[]
QED

Theorem rewrite_inline_inst_no_return:
  !args outs ret inst pi ri.
    MEM ri (FST (rewrite_inline_inst args outs ret inst pi)) ==>
    ri.inst_opcode <> RET /\ ri.inst_opcode <> RETFMP
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  `ri = inst` by
    (irule rewrite_inline_inst_survivor >> simp[] >> metis_tac[]) >>
  gvs[rewrite_inline_inst_def, is_param_opcode_def, MEM_MAPi] >>
  gvs[instruction_component_equality]
QED

Theorem rewrite_inline_insts_survivor:
  !insts args outs ret pi ris pi' ri.
    rewrite_inline_insts args outs ret insts pi = (ris,pi') /\
    MEM ri ris /\ ri.inst_opcode <> ASSIGN /\ ri.inst_opcode <> JMP ==>
    MEM ri insts
Proof
  Induct >> simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[rewrite_inline_inst_survivor, pairTheory.FST]
QED

Theorem rewrite_inline_insts_no_return:
  !insts args outs ret pi ris pi' ri.
    rewrite_inline_insts args outs ret insts pi = (ris,pi') /\
    MEM ri ris ==>
    ri.inst_opcode <> RET /\ ri.inst_opcode <> RETFMP
Proof
  Induct >> simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[rewrite_inline_inst_no_return, pairTheory.FST]
QED

Theorem rewrite_inline_block_survivor:
  !bb args outs ret pi bb' pi' ri.
    rewrite_inline_block args outs ret bb pi = (bb',pi') /\
    MEM ri bb'.bb_instructions /\
    ri.inst_opcode <> ASSIGN /\ ri.inst_opcode <> JMP ==>
    MEM ri bb.bb_instructions
Proof
  rpt gen_tac >> simp[rewrite_inline_block_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[rewrite_inline_insts_survivor]
QED

Theorem rewrite_inline_block_no_return:
  !bb args outs ret pi bb' pi' ri.
    rewrite_inline_block args outs ret bb pi = (bb',pi') /\
    MEM ri bb'.bb_instructions ==>
    ri.inst_opcode <> RET /\ ri.inst_opcode <> RETFMP
Proof
  rpt gen_tac >> simp[rewrite_inline_block_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[rewrite_inline_insts_no_return]
QED

Theorem rewrite_inline_blocks_survivor:
  !bbs args outs ret pi bbs' pi' bb' ri.
    rewrite_inline_blocks args outs ret bbs pi = (bbs',pi') /\
    MEM bb' bbs' /\ MEM ri bb'.bb_instructions /\
    ri.inst_opcode <> ASSIGN /\ ri.inst_opcode <> JMP ==>
    ?bb. MEM bb bbs /\ MEM ri bb.bb_instructions
Proof
  Induct >> simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[rewrite_inline_block_survivor]
QED

Theorem rewrite_inline_blocks_no_return:
  !bbs args outs ret pi bbs' pi' bb' ri.
    rewrite_inline_blocks args outs ret bbs pi = (bbs',pi') /\
    MEM bb' bbs' /\ MEM ri bb'.bb_instructions ==>
    ri.inst_opcode <> RET /\ ri.inst_opcode <> RETFMP
Proof
  Induct >> simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[rewrite_inline_block_no_return]
QED

Theorem clone_instruction_call_signature:
  !inst p labels target args.
    inst.inst_operands = Label target::args /\ ~MEM target labels ==>
    (clone_instruction p labels inst).inst_operands =
      Label target::MAP (clone_operand p labels) args /\
    LENGTH (clone_instruction p labels inst).inst_outputs =
      LENGTH inst.inst_outputs /\
    (clone_instruction p labels inst).inst_opcode = inst.inst_opcode
Proof
  simp[clone_instruction_def, clone_operand_def]
QED

Theorem clone_instruction_return_arity:
  !inst p labels.
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
    raw_return_user_arity (clone_instruction p labels inst) =
      raw_return_user_arity inst
Proof
  rpt strip_tac >>
  simp[clone_instruction_def, callLayoutDefsTheory.raw_return_user_arity_def,
       listTheory.NULL_EQ]
QED

Theorem inline_call_site_return_origin:
  !caller callee p ret lbl idx inst.
    MEM inst (fn_insts (inline_call_site p ret caller callee lbl idx)) /\
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
    MEM inst (fn_insts caller)
Proof
  rpt gen_tac >>
  Cases_on `lookup_block lbl caller.fn_blocks`
  >- simp[inline_call_site_def] >>
  simp[inline_call_site_def] >> pairarg_tac >> simp[] >>
  simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
       replace_block_def, MEM_MAP] >>
  rpt strip_tac >> gvs[SF boolSimps.COND_elim_ss,
                         instruction_component_equality] >>
  metis_tac[rewrite_inline_blocks_no_return,
            venomExecProofsTheory.lookup_block_MEM,
            rich_listTheory.MEM_TAKE, rich_listTheory.MEM_DROP_IMP]
QED

(* Static instruction projections are insensitive to ID renumbering. *)
Theorem renumber_insts_projection[local]:
  !insts n acc n' res f.
    (!i k. f (i with inst_id := k) = f i) /\
    FOLDL (\(id,acc) i. (id + 1n, acc ++ [i with inst_id := id]))
      (n,acc) insts = (n',res) ==>
    MAP f res = MAP f (acc ++ insts)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem renumber_block_projection:
  !n bb f.
    (!i k. f (i with inst_id := k) = f i) ==>
    MAP f (SND (renumber_block_inst_ids n bb)).bb_instructions =
      MAP f bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  simp[renumber_block_inst_ids_def] >> pairarg_tac >> simp[] >>
  drule_all renumber_insts_projection >> simp[]
QED

Theorem renumber_blocks_projection[local]:
  !bbs n acc n' res f.
    (!i k. f (i with inst_id := k) = f i) /\
    FOLDL (\(n,acc) bb.
      let (n',bb') = renumber_block_inst_ids n bb in (n',acc ++ [bb']))
      (n,acc) bbs = (n',res) ==>
    FLAT (MAP (\bb. MAP f bb.bb_instructions) res) =
    FLAT (MAP (\bb. MAP f bb.bb_instructions) (acc ++ bbs))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `FOLDL _ _ _ = _` mp_tac >> simp[Once FOLDL] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[LET_THM] >>
  first_x_assum drule_all >> simp[MAP_APPEND, APPEND_ASSOC] >>
  drule renumber_block_projection >>
  disch_then (qspecl_then [`n`, `h`] mp_tac) >> simp[]
QED

Theorem renumber_fn_projection:
  !fn f.
    (!i k. f (i with inst_id := k) = f i) ==>
    MAP f (fn_insts (renumber_fn_inst_ids fn)) = MAP f (fn_insts fn)
Proof
  rpt gen_tac >> strip_tac >>
  simp[renumber_fn_inst_ids_def] >> pairarg_tac >> simp[] >>
  drule_all (SRULE [LET_THM] renumber_blocks_projection) >>
  simp[fn_insts_def, fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o,
       combinTheory.o_DEF]
QED

Theorem fix_inline_phis_nonphi_origin:
  !old new bb fn inst.
    MEM inst (fn_insts (fix_inline_phis old new bb fn)) /\
    inst.inst_opcode <> PHI ==>
    MEM inst (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[fix_inline_phis_def, fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff, MEM_MAP] >>
  rpt strip_tac >>
  gvs[SF boolSimps.COND_elim_ss, MEM_MAP, subst_label_inst_def,
      instruction_component_equality] >>
  metis_tac[instruction_component_equality]
QED

Theorem renumber_fn_inst_projection_origin:
  !f fn inst.
    (!i k. f (i with inst_id := k) = f i) /\
    MEM inst (fn_insts (renumber_fn_inst_ids fn)) ==>
    ?orig. MEM orig (fn_insts fn) /\ f orig = f inst
Proof
  rpt strip_tac >> drule renumber_fn_projection >>
  disch_then (qspec_then `fn` assume_tac) >>
  `MEM (f inst) (MAP f (fn_insts fn))` by metis_tac[MEM_MAP] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem inline_one_site_return_origin:
  !caller callee ist caller' ist' inst.
    inline_one_site caller callee ist = SOME (caller',ist') /\
    MEM inst (fn_insts caller') /\
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
    ?orig. MEM orig (fn_insts caller) /\
      orig.inst_opcode = inst.inst_opcode /\
      raw_return_user_arity orig = raw_return_user_arity inst
Proof
  rpt gen_tac >> simp[inline_one_site_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pos last) (Q.ISPEC `\i. (i.inst_opcode, raw_return_user_arity i)`
    renumber_fn_inst_projection_origin) >>
  (impl_tac >- simp[callLayoutDefsTheory.raw_return_user_arity_def,
                        dretShapeDefsTheory.parse_dret_shape_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `MEM inst (fn_insts (renumber_fn_inst_ids _))` kall_tac >>
  qpat_x_assum `MEM orig _` mp_tac >> CASE_TAC >> simp[] >> strip_tac >>
  `orig.inst_opcode <> PHI` by simp[] >>
  metis_tac[fix_inline_phis_nonphi_origin, inline_call_site_return_origin]
QED

Theorem inliner_fn_origin_returns:
  !ctx n fn. inliner_fn_origin ctx n fn ==>
    ?root. MEM root ctx.ctx_functions /\ root.fn_name = fn.fn_name /\
      !inst. MEM inst (fn_insts fn) /\
        (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
        ?orig. MEM orig (fn_insts root) /\
          orig.inst_opcode = inst.inst_opcode /\
          raw_return_user_arity orig = raw_return_user_arity inst
Proof
  ho_match_mp_tac inliner_fn_origin_ind >> rpt conj_tac
  >- (rpt strip_tac >> qexists_tac `fn` >> simp[] >> metis_tac[])
  >- metis_tac[]
  >> rpt gen_tac >> strip_tac >>
  drule inline_one_site_name >> strip_tac >>
  qexists_tac `root` >> simp[] >> rpt strip_tac >>
  metis_tac[inline_one_site_return_origin]
QED

Theorem inline_call_site_invoke_origin:
  !caller callee p ret lbl idx inst.
    MEM inst (fn_insts (inline_call_site p ret caller callee lbl idx)) /\
    inst.inst_opcode = INVOKE ==>
    MEM inst (fn_insts caller) \/
    MEM inst (fn_insts (clone_function p callee))
Proof
  rpt gen_tac >>
  Cases_on `lookup_block lbl caller.fn_blocks`
  >- simp[inline_call_site_def] >>
  simp[inline_call_site_def] >> pairarg_tac >> simp[] >>
  simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
       replace_block_def, MEM_MAP] >>
  rpt strip_tac >> gvs[SF boolSimps.COND_elim_ss,
                         instruction_component_equality]
  >- (disj1_tac >> metis_tac[venomExecProofsTheory.lookup_block_MEM,
                            rich_listTheory.MEM_TAKE])
  >- (disj1_tac >> metis_tac[])
  >- (disj1_tac >> metis_tac[venomExecProofsTheory.lookup_block_MEM,
                            rich_listTheory.MEM_DROP_IMP])
  >> disj2_tac >>
  `inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> JMP` by simp[] >>
  drule_all rewrite_inline_blocks_survivor >> simp[]
QED

Theorem clone_function_inst_origin:
  !p fn inst.
    MEM inst (fn_insts (clone_function p fn)) ==>
    ?orig. MEM orig (fn_insts fn) /\
      inst = clone_instruction p (fn_labels fn) orig
Proof
  simp[clone_function_def, fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff, MEM_MAP,
       clone_basic_block_def] >> rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]
QED

Theorem inline_one_site_invoke_origin:
  !caller callee ist caller' ist' inst.
    inline_one_site caller callee ist = SOME (caller',ist') /\
    MEM inst (fn_insts caller') /\ inst.inst_opcode = INVOKE ==>
    ?orig. (MEM orig (fn_insts caller) \/
      MEM orig (fn_insts (clone_function (inline_prefix ist.is_inline_count) callee))) /\
      orig.inst_opcode = INVOKE /\
      orig.inst_operands = inst.inst_operands /\
      orig.inst_outputs = inst.inst_outputs
Proof
  rpt gen_tac >> simp[inline_one_site_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pos last) (Q.ISPEC `\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)`
    renumber_fn_inst_projection_origin) >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM inst (fn_insts (renumber_fn_inst_ids _))` kall_tac >>
  qpat_x_assum `MEM orig _` mp_tac >> CASE_TAC >> simp[] >> strip_tac >>
  `orig.inst_opcode <> PHI` by simp[] >>
  metis_tac[fix_inline_phis_nonphi_origin, inline_call_site_invoke_origin]
QED

Theorem inliner_reachable_call_rank:
  !ctx fn inst target args (rank : string -> num).
    inliner_input_ok ctx /\ MEM fn ctx.ctx_functions /\
    fcg_is_reachable (fcg_analyze ctx) fn.fn_name /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label target::args /\
    (!caller callee.
      MEM callee (fcg_get_callees (fcg_analyze ctx) caller) ==>
      rank callee < rank caller) ==>
    rank target < rank fn.fn_name
Proof
  rpt strip_tac >>
  `ctx_wf ctx` by gvs[inliner_input_ok_def] >>
  `lookup_function fn.fn_name ctx.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[venomWfTheory.ctx_wf_def, venomWfTheory.ctx_distinct_fn_names_def,
         ctx_fn_names_def]) >>
  `fn_directly_calls ctx fn.fn_name target` by
    (simp[fcgDefsTheory.fn_directly_calls_def] >> metis_tac[]) >>
  drule_all fcg_analyze_callees_complete >> metis_tac[]
QED

Theorem inliner_reachable_call_target_external:
  !ctx fn inst target args.
    inliner_input_ok ctx /\ MEM fn ctx.ctx_functions /\
    fcg_is_reachable (fcg_analyze ctx) fn.fn_name /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label target::args ==>
    ~MEM target (fn_labels fn)
Proof
  rpt strip_tac >>
  `?rank : string -> num. !caller callee.
    MEM callee (fcg_get_callees (fcg_analyze ctx) caller) ==>
    rank callee < rank caller` by metis_tac[inliner_input_ok_def] >>
  `rank target < rank fn.fn_name` by
    (irule inliner_reachable_call_rank >> metis_tac[]) >>
  `target <> fn.fn_name` by (spose_not_then assume_tac >> gvs[]) >>
  `wf_invoke_targets ctx` by metis_tac[inliner_input_ok_def] >>
  qpat_x_assum `wf_invoke_targets ctx` mp_tac >>
  rewrite_tac[venomWfTheory.wf_invoke_targets_def] >>
  disch_then (qspecl_then [`fn`, `inst`] mp_tac) >> simp[] >> strip_tac >>
  gvs[ctx_fn_names_def, MEM_MAP] >>
  metis_tac[inliner_input_ok_def]
QED

(* Qualified static provenance: arbitrary callers, but only original-reachable
   callees may be cloned.  Erasure retains the unrestricted structural API. *)
Inductive qualified_origin:
  (!ctx fn.
    inliner_input_ok ctx /\ MEM fn ctx.ctx_functions ==>
    qualified_origin ctx 0 fn) /\
  (!ctx n m fn.
    qualified_origin ctx n fn /\ n <= m ==>
    qualified_origin ctx m fn) /\
  (!ctx n caller callee ist caller' ist'.
    qualified_origin ctx n caller /\ qualified_origin ctx n callee /\
    fcg_is_reachable (fcg_analyze ctx) callee.fn_name /\
    ist.is_inline_count = n /\
    inline_one_site caller callee ist = SOME (caller',ist') ==>
    qualified_origin ctx ist'.is_inline_count caller')
End

Theorem qualified_origin_init:
  !ctx fn. inliner_input_ok ctx /\ MEM fn ctx.ctx_functions ==>
    qualified_origin ctx 0 fn
Proof
  metis_tac[qualified_origin_rules]
QED

Theorem qualified_origin_weaken:
  !ctx n m fn. qualified_origin ctx n fn /\ n <= m ==>
    qualified_origin ctx m fn
Proof
  metis_tac[qualified_origin_rules]
QED

Theorem qualified_origin_erasure:
  !ctx n fn. qualified_origin ctx n fn ==> inliner_fn_origin ctx n fn
Proof
  ho_match_mp_tac qualified_origin_ind >> rpt conj_tac >>
  metis_tac[inliner_fn_origin_rules]
QED

Theorem qualified_origin_name:
  !ctx n fn. qualified_origin ctx n fn ==>
    ?root. MEM root ctx.ctx_functions /\ root.fn_name = fn.fn_name
Proof
  metis_tac[qualified_origin_erasure, inliner_fn_origin_name]
QED

Theorem qualified_origin_returns:
  !ctx n fn. qualified_origin ctx n fn ==>
    ?root. MEM root ctx.ctx_functions /\ root.fn_name = fn.fn_name /\
      !inst. MEM inst (fn_insts fn) /\
        (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
        ?orig. MEM orig (fn_insts root) /\
          orig.inst_opcode = inst.inst_opcode /\
          raw_return_user_arity orig = raw_return_user_arity inst
Proof
  metis_tac[qualified_origin_erasure, inliner_fn_origin_returns]
QED
