(* Mixed tuple stores retain a fixed physical source envelope. *)
Theory tupleWidenedStores
Ancestors
  tupleWidenedTargetStore tupleWidenedStoreOpen tupleTargetStoreRun tupleTargetStoreProps
  bodyMemAssignTupleTargetsStore stmtLoweringMono tupleLocalStoreRun
  exprLoweringProps tupleMemoryFrame valueEncodingProofs freshWrites
  tupleAssignParts fragExec valueEncoding
  stmtLowering compileEnv vyperInterpreter vyperState context fragGasPathMem

Theorem tuple_widened_stores_path_mem:
  !gs tys tvs dtys dtvs vs ops addr b sz ctx func cenv cx es es' s st st' d.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (INL (),es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    LENGTH dtys = LENGTH gs /\ LENGTH dtvs = LENGTH gs /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i dtvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i dtys) (EL i dtvs) /\
       tuple_target_layout es.scopes (EL i gs) (EL i dtys) (EL i dtvs) (EL i vs) /\
       (is_word_type (EL i tys) = is_word_type (EL i dtys)) /\
       type_widens_to (get_tenv cx) (EL i tys) (EL i dtys) /\
       evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
       value_has_type (EL i tvs) (EL i vs) /\ val_wf (EL i tvs) (EL i vs) /\
       value_has_type (EL i dtvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs) /\
       (is_word_type (EL i dtys) ==> type_memory_size (EL i dtvs) = 32) /\
       (~is_word_type (EL i tys) ==> type_memory_size (EL i dtvs) + 64 < dimword (:256))) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
       type_memory_bytes cenv ty = type_memory_size tv) /\ cenv.ce_target CapMcopy /\
    b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
    b + sz <= s.vs_alloca_next /\ b + sz < dimword (:256) /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    (!name lb len. local_region cenv es.scopes s name lb len ==>
       regions_disjoint b sz lb len) /\
    tuple_in_memory vs tvs addr s.vs_memory /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    (~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        alloca_history func t /\ return_buf_frame d cenv st' t /\
        s.vs_alloca_next <= t.vs_alloca_next /\ gas_path_mem ctx func s 0 (OK t) /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es'.scopes t name b sz)) /\
        (!name lb len. local_region cenv es'.scopes t name lb len ==>
           regions_disjoint b sz lb len)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      gvs[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def] >>
      qexists_tac `s` >> simp[cj 1 gas_path_mem_rules] >> metis_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!tys tvs dtys dtvs vs ops addr b sz ctx func cenv cx es es' s st st' d. _`
    (mk_asm "ih") >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  namedCases_on `dtys` ["", "dty dtys1"] >- fs[] >>
  namedCases_on `dtvs` ["", "dtv dtvs1"] >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all tuple_target_list_cons_success >> strip_tac >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  suspend "head"
QED

Resume tuple_widened_stores_path_mem[head]:
  qpat_assum `compile_tuple_store_all _ [_] _ _ _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 _ _ _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    (irule fn_has_code_split >> simp[]) >>
  drule_at (Pat `compile_tuple_store_all _ [_] _ _ _ = _`)
    tuple_target_widened_head_path_mem >>
  disch_then (drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `tuple_target_aligned _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  (impl_tac >- suspend "head_premises") >>
  disch_then (qx_choose_then `s1` (map_every assume_tac o CONJUNCTS)) >>
  suspend "tail"
QED

Resume tuple_widened_stores_path_mem[head_premises]:
  asm_rewrite_tac [] >>
  conj_tac >- suspend "head_operand" >> fs[]
QED

Resume tuple_widened_stores_path_mem[head_operand]:
  qpat_x_assum `ih :- _` kall_tac >>
  qpat_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `is_word_type ty` >- fs[] >>
  gns[val_in_memory_def, type_memory_size_def] >>
  suspend "head_nonword"
QED

Resume tuple_widened_stores_path_mem[head_nonword]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[tuple_target_layout_local] >>
  `w2n dw + sz' <= s.vs_alloca_next /\ type_memory_size entry.type <= sz'` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> qexistsl_tac [`ctx`, `func`] >>
     fs[stmt_state_rel_def]) >>
  conj_tac >- gvs[] >>
  `regions_disjoint b sz (w2n dw) sz'` by
    (first_x_assum irule >> simp[local_region_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Resume tuple_widened_stores_path_mem[tail]:
  `tuple_in_memory (v::vs1) (tv::tvs1) addr s1.vs_memory` by
    (qpat_assum `stmt_state_rel _ _ _ _ es s`
       (mp_then Any mp_tac tuple_target_widened_source_memory) >>
     disch_then (drule_at (Pat `tuple_target_layout _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `tuple_in_memory _ _ _ _`)) >>
     disch_then (qspecl_then [`s1`, `sz`, `b`] mp_tac) >>
     disch_then irule >> asm_rewrite_tac []) >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all tuple_owned_source_region_frame >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_x "ih" drule >> disch_then drule >>
  disch_then (qspecl_then [`tvs1`, `dtys1`, `dtvs1`,
    `addr + type_memory_size tv`, `b`, `sz`, `ctx`, `func`, `s1`] mp_tac) >>
  disch_then (qspec_then `d` mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >> suspend "compose"
QED

Resume tuple_widened_stores_path_mem[tail_premises]:
  asm_rewrite_tac [] >>
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- suspend "tail_fresh"
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[])
  >- fs[val_wf_def]
  >- suspend "tail_operands"
  >- suspend "tail_layout"
  >- simp[]
  >- fs[type_memory_size_def]
  >- simp[]
  >> fs[val_in_memory_def]
QED

Resume tuple_widened_stores_path_mem[tail_fresh]:
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  irule not_fresh_at_mono >> qexists_tac `st` >> simp[] >> metis_tac[]
QED

Resume tuple_widened_stores_path_mem[tail_operands]:
  `!i. i < LENGTH ops1 ==>
       eval_operand (EL i ops1) s1 = eval_operand (EL i ops1) s` by
    (qpat_assum `EVERY (\op. ?x. op = Var x) _` mp_tac >>
     qpat_assum `EVERY (\op. !x. op = Var x ==> not_fresh_at st x) _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x s1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[listTheory.EVERY_DEF, listTheory.EVERY_EL] >>
     qpat_x_assum `!n. n < LENGTH ops1 ==> ?x. _`
       (qspec_then `i` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `tailvar` assume_tac) >>
     qpat_x_assum `!n. n < LENGTH ops1 ==> !x. _`
       (qspec_then `i` mp_tac) >> simp[] >>
     strip_tac >>
     simp[venomStateTheory.eval_operand_def]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> ?w. _`
    (qspec_then `SUC i` mp_tac) >>
  pure_rewrite_tac [listTheory.LENGTH, listTheory.EL, listTheory.HD,
    listTheory.TL, listTheory.TAKE_def, listTheory.MAP, listTheory.SUM,
    prim_recTheory.LESS_MONO_EQ] >>
  `i < LENGTH ops1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH ops1 ==> eval_operand _ _ = _`
    (qspec_then `i` mp_tac) >>
  pure_asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Resume tuple_widened_stores_path_mem[tail_layout]:
  drule tuple_target_layout_transport >> disch_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp[] >>
  `i < LENGTH vs1` by fs[] >> simp[]
QED

Resume tuple_widened_stores_path_mem[compose]:
  conj_tac
  >- (strip_tac >>
      `~block_is_terminated sm` by
        (drule_all tuple_store_widened_singleton_open >> simp[]) >> simp[]) >>
  qpat_x_assum `?t. stmt_state_rel _ _ _ _ _ t /\ _`
    (qx_choose_then `sf` (map_every assume_tac o CONJUNCTS)) >>
  qexists_tac `sf` >> asm_rewrite_tac [] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  irule (gas_path_mem_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  first_assum (irule_at Any) >> simp[]
QED

Finalise tuple_widened_stores_path_mem
