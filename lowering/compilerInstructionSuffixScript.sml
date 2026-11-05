(* Generic algebra for the instructions appended by a compiler action. *)
Theory compilerInstructionSuffix
Ancestors
  loweringShapeDefs loweringShapeRules compileEnv exprLoweringProps abiEncoderProps list
  emitHelper context venomInst rich_list fragExec localPtrsProps

Theorem added_insts_append:
  cs_extends a b /\ cs_extends b c ==>
  added_insts a c = added_insts a b ++ added_insts b c
Proof
  strip_tac >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  `state_insts c = state_insts b ++ added_insts b c` by
    simp[state_insts_cs_extends] >>
  `state_insts b = state_insts a ++ added_insts a b` by
    simp[state_insts_cs_extends] >>
  `state_insts c = state_insts a ++ added_insts a c` by
    simp[state_insts_cs_extends] >>
  gvs[APPEND_ASSOC]
QED

Theorem added_insts_bind_every:
  (!s. ci_mono s (SND (m s)) /\ EVERY P (added_insts s (SND (m s)))) /\
  (!v s. ci_mono s (SND (k v s)) /\ EVERY P (added_insts s (SND (k v s)))) ==>
  !s. ci_mono s (SND (comp_bind m k s)) /\
      EVERY P (added_insts s (SND (comp_bind m k s)))
Proof
  strip_tac >> gen_tac >> Cases_on `m s` >> rename1 `m s = (v,b)` >>
  Cases_on `k v b` >> rename1 `k v b = (w,c)` >>
  `ci_mono s b /\ EVERY P (added_insts s b)` by metis_tac[pairTheory.SND] >>
  `ci_mono b c /\ EVERY P (added_insts b c)` by metis_tac[pairTheory.SND] >>
  simp[comp_bind_def] >> conj_tac
  >- (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends s b /\ cs_extends b c` by fs[ci_mono_def] >>
  drule_all added_insts_append >> disch_then SUBST1_TAC >> simp[]
QED

Theorem added_insts_ignore_every:
  (!s. ci_mono s (SND (m s)) /\ EVERY P (added_insts s (SND (m s)))) /\
  (!s. ci_mono s (SND (k s)) /\ EVERY P (added_insts s (SND (k s)))) ==>
  !s. ci_mono s (SND (comp_ignore_bind m k s)) /\
      EVERY P (added_insts s (SND (comp_ignore_bind m k s)))
Proof
  strip_tac >>
  `comp_ignore_bind m k = comp_bind m (\v. k)` by
    simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def] >>
  simp[] >> irule added_insts_bind_every >> simp[]
QED

Theorem added_insts_return_every:
  ci_mono s (SND (comp_return v s)) /\
  EVERY P (added_insts s (SND (comp_return v s)))
Proof
  simp[comp_return_def, ci_mono_refl, added_insts_def]
QED

Theorem added_insts_coverage_append:
  ci_mono a b /\ ci_mono b c /\
  (!id. id IN frag_ids a b ==>
    ?i. MEM i (added_insts a b) /\ i.inst_id = id) /\
  (!id. id IN frag_ids b c ==>
    ?i. MEM i (added_insts b c) /\ i.inst_id = id) ==>
  !id. id IN frag_ids a c ==>
    ?i. MEM i (added_insts a c) /\ i.inst_id = id
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c` by fs[ci_mono_def] >>
  drule_all added_insts_append >> disch_then SUBST1_TAC >>
  simp[MEM_APPEND] >>
  fs[frag_ids_def, ci_mono_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
    arithmeticTheory.NOT_LESS]
QED

Theorem added_insts_emit_op:
  emit_op opc ops sa = (op,sb) ==>
  ?q. op = Var q /\ ~not_fresh_at sa q /\
    added_insts sa sb = [mk_inst sa.cs_next_id opc ops [q]] /\
    sb.cs_next_id = sa.cs_next_id + 1 /\ ci_mono sa sb
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  qexists_tac `out` >> simp[added_insts_def, DROP_LENGTH_APPEND] >>
  conj_tac >- gvs[emit_op_eq] >>
  mp_tac ci_mono_emit_op >> disch_then (qspecl_then [`opc`, `ops`, `sa`] mp_tac) >>
  simp[]
QED

Theorem added_insts_emit_void:
  emit_void opc ops sa = (v,sb) ==>
  added_insts sa sb = [mk_inst sa.cs_next_id opc ops []] /\
  sb.cs_next_id = sa.cs_next_id + 1 /\ ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono sa sb` by
    (mp_tac ci_mono_emit_void >>
     disch_then (qspecl_then [`opc`, `ops`, `sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_eq] >> strip_tac >> gvs[] >>
  simp[added_insts_def, state_insts_def, all_blocks_def,
       DROP_APPEND, DROP_LENGTH_APPEND]
QED

Theorem added_insts_allocate:
  compile_alloc_buffer n sa = (buf,sb) ==>
  ?q. buf.buf_operand = Var q /\ ~not_fresh_at sa q /\
    added_insts sa sb = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]] /\
    sb.cs_next_id = sa.cs_next_id + 1 /\ ci_mono sa sb
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w n)] sa` >>
  simp[] >> strip_tac >> gvs[] >>
  drule added_insts_emit_op >> simp[]
QED

Theorem added_insts_emit_inst:
  emit_inst opc ops outs sa = (v,sb) ==>
  added_insts sa sb = [mk_inst sa.cs_next_id opc ops outs] /\
  sb.cs_next_id = sa.cs_next_id + 1 /\ ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono sa sb` by
    (mp_tac ci_mono_emit_inst >>
     disch_then (qspecl_then [`opc`, `ops`, `outs`, `sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[added_insts_def, state_insts_def, all_blocks_def, DROP_APPEND]
QED

Theorem added_insts_fresh_label:
  fresh_label tag sa = (lbl,sb) ==>
  added_insts sa sb = [] /\ sb.cs_next_id = sa.cs_next_id /\ ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono sa sb` by
    (mp_tac ci_mono_fresh_label >>
     disch_then (qspecl_then [`tag`, `sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `fresh_label _ _ = _` mp_tac >>
  simp[fresh_label_def] >> strip_tac >> gvs[] >>
  simp[added_insts_def, state_insts_def, all_blocks_def]
QED

Theorem added_insts_new_block:
  new_block lbl sa = (v,sb) ==>
  added_insts sa sb = [] /\ sb.cs_next_id = sa.cs_next_id /\ ci_mono sa sb
Proof
  strip_tac >>
  `ci_mono sa sb` by
    (mp_tac ci_mono_new_block >>
     disch_then (qspecl_then [`lbl`, `sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `new_block _ _ = _` mp_tac >>
  simp[new_block_def] >> strip_tac >> gvs[] >>
  simp[added_insts_def, state_insts_def, all_blocks_def, DROP_APPEND]
QED

Theorem added_insts_bind_coverage:
  (!s. ci_mono s (SND (m s)) /\
    !id. id IN frag_ids s (SND (m s)) ==>
      ?i. MEM i (added_insts s (SND (m s))) /\ i.inst_id = id) /\
  (!v s. ci_mono s (SND (k v s)) /\
    !id. id IN frag_ids s (SND (k v s)) ==>
      ?i. MEM i (added_insts s (SND (k v s))) /\ i.inst_id = id) ==>
  !s. ci_mono s (SND (comp_bind m k s)) /\
    !id. id IN frag_ids s (SND (comp_bind m k s)) ==>
      ?i. MEM i (added_insts s (SND (comp_bind m k s))) /\ i.inst_id = id
Proof
  strip_tac >> gen_tac >> Cases_on `m s` >> rename1 `m s = (v,b)` >>
  Cases_on `k v b` >> rename1 `k v b = (w,c)` >>
  first_x_assum (qspecl_then [`v`, `b`] mp_tac) >>
  first_x_assum (qspec_then `s` mp_tac) >> simp[] >>
  ntac 2 (disch_then strip_assume_tac) >>
  gvs[comp_bind_def] >> conj_tac
  >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[added_insts_coverage_append]
QED

Theorem added_insts_ignore_coverage:
  (!s. ci_mono s (SND (m s)) /\
    !id. id IN frag_ids s (SND (m s)) ==>
      ?i. MEM i (added_insts s (SND (m s))) /\ i.inst_id = id) /\
  (!s. ci_mono s (SND (k s)) /\
    !id. id IN frag_ids s (SND (k s)) ==>
      ?i. MEM i (added_insts s (SND (k s))) /\ i.inst_id = id) ==>
  !s. ci_mono s (SND (comp_ignore_bind m k s)) /\
    !id. id IN frag_ids s (SND (comp_ignore_bind m k s)) ==>
      ?i. MEM i (added_insts s (SND (comp_ignore_bind m k s))) /\ i.inst_id = id
Proof
  strip_tac >>
  `comp_ignore_bind m k = comp_bind m (\v. k)` by
    simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def] >>
  simp[] >> irule added_insts_bind_coverage >> simp[]
QED

Theorem added_insts_single_coverage:
  b.cs_next_id = a.cs_next_id + 1 /\
  added_insts a b = [mk_inst a.cs_next_id opc ops outs] ==>
  !id. id IN frag_ids a b ==>
    ?i. MEM i (added_insts a b) /\ i.inst_id = id
Proof
  simp[frag_ids_def, mk_inst_def]
QED

Theorem added_insts_same_id_coverage:
  b.cs_next_id = a.cs_next_id ==>
  !id. id IN frag_ids a b ==>
    ?i. MEM i (added_insts a b) /\ i.inst_id = id
Proof
  simp[frag_ids_def]
QED

(* Relative properties, such as output freshness, weaken toward the start
   of a monotone compiler sequence. *)
Theorem added_insts_bind_relative_every:
  (!a b i. ci_mono a b /\ P b i ==> P a i) /\
  (!s. ci_mono s (SND (m s)) /\ EVERY (P s) (added_insts s (SND (m s)))) /\
  (!v s. ci_mono s (SND (k v s)) /\ EVERY (P s) (added_insts s (SND (k v s)))) ==>
  !s. ci_mono s (SND (comp_bind m k s)) /\
      EVERY (P s) (added_insts s (SND (comp_bind m k s)))
Proof
  strip_tac >> gen_tac >> Cases_on `m s` >> rename1 `m s = (v,b)` >>
  Cases_on `k v b` >> rename1 `k v b = (w,c)` >>
  `ci_mono s b /\ EVERY (P s) (added_insts s b)` by metis_tac[pairTheory.SND] >>
  `ci_mono b c /\ EVERY (P b) (added_insts b c)` by metis_tac[pairTheory.SND] >>
  simp[comp_bind_def] >> conj_tac
  >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends s b /\ cs_extends b c` by fs[ci_mono_def] >>
  drule_all added_insts_append >> disch_then SUBST1_TAC >>
  simp[EVERY_APPEND] >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem added_insts_ignore_relative_every:
  (!a b i. ci_mono a b /\ P b i ==> P a i) /\
  (!s. ci_mono s (SND (m s)) /\ EVERY (P s) (added_insts s (SND (m s)))) /\
  (!s. ci_mono s (SND (k s)) /\ EVERY (P s) (added_insts s (SND (k s)))) ==>
  !s. ci_mono s (SND (comp_ignore_bind m k s)) /\
      EVERY (P s) (added_insts s (SND (comp_ignore_bind m k s)))
Proof
  strip_tac >>
  `comp_ignore_bind m k = comp_bind m (\v. k)` by
    simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def] >>
  simp[] >> irule added_insts_bind_relative_every >> metis_tac[]
QED

Theorem added_insts_allocate32_every:
  ci_mono sa (SND (compile_alloc_buffer 32 sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==>
    i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (compile_alloc_buffer 32 sa)))
Proof
  Cases_on `compile_alloc_buffer 32 sa` >>
  drule added_insts_allocate >> strip_tac >> simp[mk_inst_def]
QED

Theorem allocation_shape_relative_mono:
  ci_mono a b /\
  (i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at b q) ==>
  (i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at a q)
Proof
  simp[ci_mono_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Theorem added_insts_nonalloca_op_every:
  opc <> ALLOCA ==>
  ci_mono sa (SND (emit_op opc ops sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (emit_op opc ops sa)))
Proof
  strip_tac >> Cases_on `emit_op opc ops sa` >>
  drule added_insts_emit_op >> strip_tac >> simp[mk_inst_def]
QED

Theorem added_insts_nonalloca_void_every:
  opc <> ALLOCA ==>
  ci_mono sa (SND (emit_void opc ops sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (emit_void opc ops sa)))
Proof
  strip_tac >> Cases_on `emit_void opc ops sa` >>
  drule added_insts_emit_void >> strip_tac >> simp[mk_inst_def]
QED

Theorem added_insts_nonalloca_inst_every:
  opc <> ALLOCA ==>
  ci_mono sa (SND (emit_inst opc ops outs sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (emit_inst opc ops outs sa)))
Proof
  strip_tac >> Cases_on `emit_inst opc ops outs sa` >>
  drule added_insts_emit_inst >> strip_tac >> simp[mk_inst_def]
QED

Theorem added_insts_fresh_label_every:
  ci_mono sa (SND (fresh_label tag sa)) /\
  EVERY P (added_insts sa (SND (fresh_label tag sa)))
Proof
  Cases_on `fresh_label tag sa` >>
  drule added_insts_fresh_label >> simp[]
QED

Theorem added_insts_new_block_every:
  ci_mono sa (SND (new_block lbl sa)) /\
  EVERY P (added_insts sa (SND (new_block lbl sa)))
Proof
  Cases_on `new_block lbl sa` >>
  drule added_insts_new_block >> simp[]
QED

Theorem added_insts_emit_op_coverage:
  ci_mono s (SND (emit_op opc ops s)) /\
  !id. id IN frag_ids s (SND (emit_op opc ops s)) ==>
    ?i. MEM i (added_insts s (SND (emit_op opc ops s))) /\ i.inst_id = id
Proof
  Cases_on `emit_op opc ops s` >>
  drule added_insts_emit_op >> strip_tac >> simp[] >>
  simp[frag_ids_def, mk_inst_def]
QED

Theorem added_insts_emit_void_coverage:
  ci_mono s (SND (emit_void opc ops s)) /\
  !id. id IN frag_ids s (SND (emit_void opc ops s)) ==>
    ?i. MEM i (added_insts s (SND (emit_void opc ops s))) /\ i.inst_id = id
Proof
  Cases_on `emit_void opc ops s` >>
  drule added_insts_emit_void >> strip_tac >> simp[] >>
  simp[frag_ids_def, mk_inst_def]
QED

Theorem added_insts_emit_inst_coverage:
  ci_mono s (SND (emit_inst opc ops outs s)) /\
  !id. id IN frag_ids s (SND (emit_inst opc ops outs s)) ==>
    ?i. MEM i (added_insts s (SND (emit_inst opc ops outs s))) /\ i.inst_id = id
Proof
  Cases_on `emit_inst opc ops outs s` >>
  drule added_insts_emit_inst >> strip_tac >> simp[] >>
  simp[frag_ids_def, mk_inst_def]
QED

Theorem added_insts_allocate_coverage:
  ci_mono s (SND (compile_alloc_buffer n s)) /\
  !id. id IN frag_ids s (SND (compile_alloc_buffer n s)) ==>
    ?i. MEM i (added_insts s (SND (compile_alloc_buffer n s))) /\ i.inst_id = id
Proof
  Cases_on `compile_alloc_buffer n s` >>
  drule added_insts_allocate >> strip_tac >> simp[] >>
  simp[frag_ids_def, mk_inst_def]
QED

Theorem added_insts_fresh_label_coverage:
  ci_mono s (SND (fresh_label tag s)) /\
  !id. id IN frag_ids s (SND (fresh_label tag s)) ==>
    ?i. MEM i (added_insts s (SND (fresh_label tag s))) /\ i.inst_id = id
Proof
  Cases_on `fresh_label tag s` >>
  drule added_insts_fresh_label >> strip_tac >> simp[] >>
  simp[frag_ids_def]
QED

Theorem added_insts_new_block_coverage:
  ci_mono s (SND (new_block lbl s)) /\
  !id. id IN frag_ids s (SND (new_block lbl s)) ==>
    ?i. MEM i (added_insts s (SND (new_block lbl s))) /\ i.inst_id = id
Proof
  Cases_on `new_block lbl s` >>
  drule added_insts_new_block >> strip_tac >> simp[] >>
  simp[frag_ids_def]
QED

Theorem added_insts_return_coverage:
  ci_mono s (SND (comp_return v s)) /\
  !id. id IN frag_ids s (SND (comp_return v s)) ==>
    ?i. MEM i (added_insts s (SND (comp_return v s))) /\ i.inst_id = id
Proof
  simp[comp_return_def, ci_mono_refl, frag_ids_def]
QED

Theorem added_insts_function_member:
  cs_extends sa sb /\ fn_has_code sa sb func /\
  MEM i (added_insts sa sb) ==> MEM i (fn_insts func)
Proof
  strip_tac >>
  `?new. sb.cs_blocks = new ++ sa.cs_blocks` by fs[cs_extends_def] >>
  `MEM i (FLAT (MAP (\bb. bb.bb_instructions) (REVERSE new)) ++
          sb.cs_current_insts)` by
    (qpat_x_assum `MEM i (added_insts sa sb)` mp_tac >>
     simp[added_insts_def, state_insts_def, all_blocks_def,
       REVERSE_APPEND, MAP_APPEND, FLAT_APPEND, DROP_APPEND] >>
     qmatch_goalsub_abbrev_tac `DROP (LENGTH xs + n) xs` >>
     `DROP (LENGTH xs + n) xs = []` by simp[DROP_EQ_NIL] >>
     simp[] >> metis_tac[MEM_DROP_IMP]) >>
  fs[MEM_APPEND, MEM_FLAT, MEM_MAP]
  >- (gvs[fn_has_code_def, emitted_blocks_def, TAKE_APPEND] >>
      metis_tac[lookup_block_fn_insts]) >>
  fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  metis_tac[lookup_block_fn_insts, MEM_APPEND]
QED

Theorem added_insts_function_property:
  cs_extends sa sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  EVERY P (added_insts sa sb) /\
  (!id. id IN frag_ids sa sb ==>
    ?i. MEM i (added_insts sa sb) /\ i.inst_id = id) /\
  MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids sa sb ==>
  P inst
Proof
  strip_tac >>
  `?i. MEM i (added_insts sa sb) /\ i.inst_id = inst.inst_id` by metis_tac[] >>
  `MEM i (fn_insts func)` by metis_tac[added_insts_function_member] >>
  `i = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[EVERY_MEM]
QED
