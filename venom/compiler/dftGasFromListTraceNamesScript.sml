Theory dftGasFromListTraceNames
Ancestors
  dftGasFromListTraceDefs venomExecSemantics venomInst venomState list rich_list
  arithmetic execEquivParamBase

(* A frame subtree includes its root frame. *)
Definition frame_below_def:
  frame_below root frame <=> ?extra. frame = extra ++ root
End

(* Events after entering a block are strictly deeper than its incoming depth,
   either in that frame or at the oldest additional call site. *)
Definition later_region_def:
  later_region p (d:num) ((frame,depth,id):gas_event) <=>
    (frame = p /\ d < depth) \/
    ?extra k call_id. frame = extra ++ (k,call_id)::p /\ d < k
End

(* The part owned by a block: its direct instructions and their callees. *)
Definition block_region_def:
  block_region p (d:num) ids ((frame,depth,id):gas_event) <=>
    (frame = p /\ depth = d /\ MEM id ids) \/
    ?extra call_id. frame = extra ++ (d,call_id)::p /\ MEM call_id ids
End

Theorem later_region_frame:
  later_region p d (frame,depth,id) ==> frame_below p frame
Proof
  simp[later_region_def, frame_below_def] >> strip_tac
  >- (qexists_tac `[]` >> simp[]) >>
  qexists_tac `extra ++ [(k,call_id)]` >> simp[]
QED

Theorem below_call_region:
  frame_below ((d,call_id)::p) frame /\ MEM call_id ids ==>
  block_region p d ids (frame,depth,id)
Proof
  simp[frame_below_def, block_region_def] >> metis_tac[]
QED

Theorem block_region_later:
  block_region p (SUC d) ids e ==> later_region p d e
Proof
  PairCases_on `e` >> simp[block_region_def, later_region_def] >>
  strip_tac >> gvs[] >> metis_tac[DECIDE ``d < SUC d``]
QED

Theorem later_region_mono:
  d <= k /\ later_region p k e ==> later_region p d e
Proof
  PairCases_on `e` >> simp[later_region_def] >>
  strip_tac >> gvs[] >> metis_tac[LESS_EQ_LESS_TRANS]
QED

Theorem block_region_mono:
  (!id. MEM id xs ==> MEM id ys) /\ block_region p d xs e ==>
  block_region p d ys e
Proof
  PairCases_on `e` >> simp[block_region_def] >> metis_tac[]
QED

Theorem remaining_ids_step:
  get_instruction bb idx = SOME inst ==>
  MAP (\i. i.inst_id) (DROP idx bb.bb_instructions) =
    inst.inst_id :: MAP (\i. i.inst_id) (DROP (SUC idx) bb.bb_instructions)
Proof
  simp[get_instruction_def] >> strip_tac >> gvs[] >>
  `DROP idx bb.bb_instructions =
    EL idx bb.bb_instructions :: DROP (SUC idx) bb.bb_instructions` by
    (irule DROP_CONS_EL >> simp[]) >> simp[]
QED

Theorem trace_regions:
  (!p d fuel ctx fn inst s.
    EVERY (\v. frame_below ((d,inst.inst_id)::p) (FST (FST v)))
      (trace_step p d fuel ctx fn inst s)) /\
  (!p d fuel ctx fn bb s.
    EVERY (\v. block_region p d
      (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions)) (FST v))
      (trace_block p d fuel ctx fn bb s)) /\
  (!p d fuel ctx fn s.
    EVERY (\v. later_region p d (FST v))
      (trace_blocks p d fuel ctx fn s))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_regions[step]:
  rpt gen_tac >> strip_tac >> simp[cj 1 trace_defs] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  rename1 `setup_callee _ _ _ = SOME cs` >>
  `EVERY (\v. later_region ((d,inst.inst_id)::p) d (FST v))
    (trace_blocks ((d,inst.inst_id)::p) d fuel ctx callee cs)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `v` >> PairCases_on `q` >> simp[] >>
  metis_tac[later_region_frame]
QED

Resume trace_regions[block]:
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_defs] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  drule remaining_ids_step >> strip_tac >>
  simp[Once trace_defs, EVERY_APPEND] >>
  conj_tac >- simp[block_region_def] >>
  conj_tac
  >- (`EVERY (\v. frame_below ((d,inst.inst_id)::p) (FST (FST v)))
         (trace_step p d fuel ctx fn inst s)` by
        (first_x_assum irule >> simp[]) >>
      gvs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> Cases_on `v` >> PairCases_on `q` >>
      simp[] >> strip_tac >> irule below_call_region >> simp[] >>
      qexists_tac `inst.inst_id` >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >> gvs[] >>
  `EVERY (\v. block_region p d
       (MAP (\i. i.inst_id) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)) (FST v))
     (trace_block p d fuel ctx fn bb (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> irule block_region_mono >>
  qexists_tac `MAP (\i. i.inst_id) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` >> simp[]
QED

Resume trace_regions[blocks]:
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[] >> rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_defs] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[]
  >- (rename1 `eval_phis _ _ = OK sp` >>
      simp[Once trace_defs, EVERY_APPEND] >> conj_tac
      >- (gvs[EVERY_MEM] >> rpt strip_tac >>
          irule block_region_later >>
          first_x_assum (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]) >>
      Cases_on `exec_block k ctx bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
      rename1 `exec_block _ _ _ _ = OK t` >>
      Cases_on `t.vs_halted` >> simp[] >> gvs[EVERY_MEM] >>
      rpt strip_tac >> irule later_region_mono >>
      qexists_tac `SUC d` >> simp[] >> metis_tac[]) >>
  simp[Once trace_defs]
QED

Finalise trace_regions

Theorem frame_call_site_unique:
  xs ++ a::p = ys ++ b::p ==> a = b
Proof
  strip_tac >>
  `xs ++ [a] = ys ++ [b]` by
    metis_tac[APPEND_11, APPEND_ASSOC, APPEND] >>
  pop_assum (mp_tac o AP_TERM ``LAST``) >> simp[LAST_APPEND]
QED

Theorem frame_not_below_self:
  ~frame_below (site::p) p
Proof
  simp[frame_below_def] >> strip_tac >>
  pop_assum (mp_tac o AP_TERM ``LENGTH``) >> simp[]
QED

Theorem block_later_disjoint:
  block_region p d ids e ==> ~later_region p d e
Proof
  PairCases_on `e` >>
  simp[block_region_def, later_region_def] >> rpt strip_tac >> gvs[]
QED

Theorem block_regions_disjoint:
  (!id. MEM id xs ==> ~MEM id ys) /\ block_region p d xs e ==>
  ~block_region p d ys e
Proof
  PairCases_on `e` >>
  simp[block_region_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[frame_call_site_unique, frame_not_below_self, frame_below_def,
            pairTheory.PAIR_EQ]
QED

Theorem trace_step_region:
  MEM v (trace_step p d fuel ctx fn inst s) ==>
  block_region p d [inst.inst_id] (FST v)
Proof
  strip_tac >>
  mp_tac (cj 1 trace_regions) >> simp[EVERY_MEM] >>
  disch_then drule >>
  Cases_on `v` >> PairCases_on `q` >> simp[] >>
  strip_tac >> irule below_call_region >> simp[]
QED

Theorem trace_block_region:
  MEM v (trace_block p d fuel ctx fn bb s) ==>
  block_region p d (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions))
    (FST v)
Proof
  mp_tac (cj 2 trace_regions) >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem trace_blocks_region:
  MEM v (trace_blocks p d fuel ctx fn s) ==> later_region p d (FST v)
Proof
  mp_tac (cj 3 trace_regions) >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem trace_step_not_root:
  ~MEM (p,d,id) (MAP FST (trace_step p d fuel ctx fn inst s))
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  assume_tac (cj 1 trace_regions) >> fs[EVERY_MEM] >>
  first_x_assum drule >>
  qpat_x_assum `(p,d,id) = FST y` (SUBST1_TAC o SYM) >>
  simp[frame_not_below_self]
QED

Theorem trace_block_excludes:
  ~MEM id (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions)) ==>
  ~MEM (p,d,id) (MAP FST (trace_block p d fuel ctx fn bb s))
Proof
  simp[MEM_MAP] >> rpt strip_tac >> drule trace_block_region >>
  qpat_x_assum `(p,d,id) = FST y` (SUBST1_TAC o SYM) >>
  simp[block_region_def, MEM_MAP] >>
  metis_tac[frame_not_below_self, frame_below_def]
QED

Theorem trace_step_block_disjoint:
  ~MEM inst.inst_id (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bb.bb_instructions)) ==>
  !e. MEM e (MAP FST (trace_step p d fuel ctx fn inst s)) ==>
      ~MEM e (MAP FST (trace_block p d fuel ctx fn bb t))
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  drule trace_step_region >> strip_tac >>
  drule trace_block_region >> strip_tac >>
  `!id. MEM id [inst.inst_id] ==>
     ~MEM id (MAP (\i. i.inst_id) (DROP t.vs_inst_idx bb.bb_instructions))` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  metis_tac[block_regions_disjoint]
QED

Theorem trace_names_distinct:
  (!p d fuel ctx fn inst s.
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
              f.fn_blocks) ctx.ctx_functions ==>
    ALL_DISTINCT (MAP FST (trace_step p d fuel ctx fn inst s))) /\
  (!p d fuel ctx fn bb s.
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
              f.fn_blocks) ctx.ctx_functions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    ALL_DISTINCT (MAP FST (trace_block p d fuel ctx fn bb s))) /\
  (!p d fuel ctx fn s.
    EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
              f.fn_blocks) ctx.ctx_functions /\
    EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) fn.fn_blocks ==>
    ALL_DISTINCT (MAP FST (trace_blocks p d fuel ctx fn s)))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_names_distinct[step]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  first_x_assum irule >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[lookup_function_MEM]
QED

Resume trace_names_distinct[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 trace_defs)] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (DROP s.vs_inst_idx bb.bb_instructions))` by
    (rewrite_tac[MAP_DROP] >> irule ALL_DISTINCT_DROP >> simp[]) >>
  drule remaining_ids_step >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (MAP FST (trace_step p d fuel ctx fn inst s))` by
    (first_x_assum irule >> simp[]) >>
  simp[Once (cj 2 trace_defs), MAP_APPEND, ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (simp[trace_step_not_root] >>
      Cases_on `step_inst fuel ctx inst s` >> simp[] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      irule trace_block_excludes >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `~MEM inst.inst_id (MAP (\i. i.inst_id)
      (DROP (t with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx bb.bb_instructions))` by simp[] >>
  metis_tac[trace_step_block_disjoint]
QED

Resume trace_names_distinct[blocks]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `fuel` >- simp[] >> rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs)] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[FIND_MEM, lookup_block_def]) >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[Once (cj 3 trace_defs)] >>
  rename1 `eval_phis _ _ = OK sp` >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND] >>
  Cases_on `run_block_non_phis k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `run_block_non_phis _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >>
  simp[MEM_MAP] >> rpt strip_tac >>
  drule trace_block_region >> strip_tac >>
  drule trace_blocks_region >> strip_tac >>
  metis_tac[block_later_disjoint]
QED

Finalise trace_names_distinct

Theorem trace_context_names_distinct:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
             f.fn_blocks) ctx.ctx_functions ==>
  ALL_DISTINCT (MAP FST (trace_context fuel ctx s))
Proof
  strip_tac >> simp[trace_context_def, trace_function_def] >>
  Cases_on `ctx.ctx_entry` >> simp[] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  irule (cj 3 trace_names_distinct) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[lookup_function_MEM]
QED

Theorem trace_gas_name_mem:
  MEM e (MAP FST (trace_gas visits)) ==> MEM e (MAP FST visits)
Proof
  Induct_on `visits` >> simp[trace_gas_def] >>
  qx_gen_tac `v` >> PairCases_on `v` >>
  simp[visit_gas_def] >> rename1 `inst.inst_opcode = GAS` >>
  Cases_on `inst.inst_opcode = GAS` >>
  gvs[trace_gas_def] >> metis_tac[]
QED

Theorem trace_gas_names_distinct:
  ALL_DISTINCT (MAP FST visits) ==>
  ALL_DISTINCT (MAP FST (trace_gas visits))
Proof
  Induct_on `visits` >> simp[trace_gas_def] >>
  qx_gen_tac `v` >> PairCases_on `v` >>
  simp[visit_gas_def] >> rename1 `inst.inst_opcode = GAS` >>
  Cases_on `inst.inst_opcode = GAS` >>
  simp[] >> metis_tac[trace_gas_name_mem, trace_gas_def]
QED

Theorem trace_context_gas_names_distinct:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
             f.fn_blocks) ctx.ctx_functions ==>
  ALL_DISTINCT (MAP FST (trace_gas (trace_context fuel ctx s)))
Proof
  metis_tac[trace_gas_names_distinct, trace_context_names_distinct]
QED
