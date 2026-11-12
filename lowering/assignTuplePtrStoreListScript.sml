(* Mixed sequential stores retain only unread robust values, not the whole
   original tuple. All operands are loaded before this phase. *)
Theory assignTuplePtrStoreList
Ancestors
  assignTuplePtrMixedHead assignTuplePtrUnread assignTuplePtrUnreadBounds
  vyperTypeDefaults valueEncodingProofs tupleTargetStoreRun tupleTargetStoreProps
  tupleMemoryFrame tupleMemoryLayout bodyPtrDefs fragGasPathPtr
  exprLoweringProps stmtLoweringMono exprSimProps stmtSimDefs tupleAssignParts fragExec
  stmtLowering vyperInterpreter vyperState context compileEnv loweringStateRelDefs
  venomState venomExecSemantics ptrDiscipline list rich_list finite_map
  valueEncoding valueEncodingDefs valueEncodingProps valueTypingMemoryProps freshWrites vyperTyping arithmetic

Theorem tuple_store_targets_path_ptr:
  !gs m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' G tn d D PG.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (INL (),es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x /\ not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    (!i. i < LENGTH gs ==>
       ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))) /\
         (!p. ~is_word_type (EL i tys) /\ EL i ops = Var p ==> ptr_covers G tn p s (type_memory_size (EL i tvs)))) /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
       tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword(:256)) /\
    (m ==> (!i. i < LENGTH tys ==>
         evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz))) /\
    fn_has_code st st' func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
    (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t G' tn'. stmt_state_rel ctx func cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def, Once evaluate_def, return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  qpat_x_assum `!m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' G tn d D PG. _`
    (mk_asm "ih") >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `ih :- _` kall_tac >> fs[value_has_type_def, val_wf_def]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all tuple_target_list_cons_success >> strip_tac >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  suspend "head"
QED

Resume tuple_store_targets_path_ptr[head]:
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    (irule fn_has_code_split >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?src. op = Var src /\ not_fresh_at st src` by fs[] >> gvs[] >>
  qpat_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  strip_tac >>
  rename1 `eval_operand (Var src) s = SOME sw` >>
  `lookup_var src s = SOME sw` by fs[eval_operand_def] >>
  `is_word_type ty ==> sw = typed_val_to_w256 tv v` by (strip_tac >> fs[]) >>
  `~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)` by
    (qpat_x_assum `!i. i < _ /\ _ ==> type_memory_size _ + 64 < _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all tuple_target_mixed_head_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `t` (qx_choose_then `G'` (qx_choose_then `tn'`
      (map_every assume_tac o CONJUNCTS))))) >>
  drule_all tuple_target_assignment_scope_frame >> strip_tac >>
  suspend "tail"
QED

Resume tuple_store_targets_path_ptr[tail]:
  asm_x "ih" drule >> disch_then drule >>
  disch_then (qspecl_then [`m`, `tvs1`, `addr + type_memory_size tv`, `b`,
    `sz`, `ctx`, `func`, `t`, `G'`, `tn'`, `d`, `D`, `PG`] mp_tac) >>
  (impl_tac >- suspend "premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >> suspend "compose"
QED

Resume tuple_store_targets_path_ptr[premises]:
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!op. MEM op ops1 ==> _` drule >> strip_tac >> gvs[] >>
      irule not_fresh_at_mono >> qexists `st` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[])
  >- fs[value_has_type_def]
  >- fs[val_wf_def]
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `st` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `st` >> simp[])
  >- suspend "resources"
  >- (drule tuple_target_layout_transport >> disch_tac >>
      gen_tac >> strip_tac >>
      qpat_x_assum `!i. i < _ ==> tuple_target_aligned _ _ _ _ _ /\ _`
        (qspec_then `SUC i` mp_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < _ /\ _ ==> type_memory_size _ + 64 < _`
        (qspec_then `SUC i` mp_tac) >> simp[])
  >- suspend "container"
  >> asm_rewrite_tac []
QED

Resume tuple_store_targets_path_ptr[resources]:
  gen_tac >> strip_tac >>
  `i < LENGTH ops1 /\ i < LENGTH tys1 /\ i < LENGTH tvs1` by fs[] >>
  `?p. EL i ops1 = Var p /\ not_fresh_at st p` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  qpat_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp_tac (srw_ss()) [] >>
  (impl_tac >- fs[]) >> strip_tac >>
  rename1 `eval_operand (EL i ops1) s = SOME w` >>
  `lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
   op_taint tn' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  `eval_operand (Var p) t = SOME w /\
   op_prov G' (Var p) = op_prov G (Var p)` by
    gvs[eval_operand_def, op_prov_def] >>
  `ptr_val_ok cx (EL i tys1) (EL i vs1) (Var p) G' tn' t` by suspend "robust" >>
  conj_tac >- gvs[] >>
  qexists `w` >> simp[] >> rpt strip_tac >> gvs[ptr_covers_def]
QED

Resume tuple_store_targets_path_ptr[robust]:
  Cases_on `is_word_type (EL i tys1)`
  >- gvs[ptr_val_ok_def] >>
  `m` by (fs[EVERY_EL] >> metis_tac[]) >>
  qpat_x_assum `m ==> _` mp_tac >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) (EL i tys1) = SOME (EL i tvs1)` by
    (qpat_x_assum `!i. i < _ ==> evaluate_type _ _ = _`
      (qspec_then `SUC i` mp_tac) >> simp[]) >>
  `values_have_types tvs1 vs1` by fs[value_has_type_def] >>
  `val_wf (EL i tvs1) (EL i vs1) /\
   addr + type_memory_size tv <= w2n w /\
   w2n w + val_footprint (EL i tvs1) (EL i vs1) <= b + sz` by
    (irule tuple_unread_element_resources_ptr >> simp[] >>
     qpat_x_assum `if is_word_type (EL i tys1) then _ else _` mp_tac >>
     simp[] >> decide_tac) >>
  qpat_x_assum `t.vs_memory = s.vs_memory /\ _ \/ _` strip_assume_tac
  >- gvs[ptr_val_ok_def, ptr_mem_ok_def] >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all tuple_container_write_position >> disch_tac >>
  suspend "robust_write"
QED

Resume tuple_store_targets_path_ptr[robust_write]:
  qpat_x_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _` kall_tac >>
  qpat_x_assum `!i. i < _ ==> tuple_target_aligned _ _ _ _ _ /\ _` kall_tac >>
  qpat_x_assum `!i. i < _ /\ _ ==> type_memory_size _ + 64 < _` kall_tac >>
  qpat_x_assum `if is_word_type ty then _ else _` kall_tac >>
  rename1 `local_region cenv es.scopes s id dst dsz` >>
  irule tuple_unread_value_frame_ptr >>
  conj_tac >- gvs[] >>
  qexistsl_tac [`G`, `addr`, `b`, `dst`, `dsz`, `type_memory_size tv`,
    `s`, `sz`, `tn`, `type_memory_size tv`] >>
  simp[eval_operand_def, op_prov_def] >>
  rpt strip_tac >> gvs[eval_operand_def]
QED

Resume tuple_store_targets_path_ptr[container]:
  strip_tac >>
  qpat_x_assum `m ==> _` mp_tac >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  conj_tac >- fs[type_memory_size_def] >>
  irule tuple_container_transport >>
  qexistsl_tac [`s`, `st`, `es.scopes`] >> simp[]
QED

Resume tuple_store_targets_path_ptr[compose]:
  `~block_is_terminated sm` by
    (drule_all tuple_store_singleton_open >> simp[]) >>
  conj_tac >- simp[] >>
  qpat_x_assum `?t' G'' tn''. _`
    (qx_choose_then `sf` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`sf`, `Gf`, `tnf`] >> asm_rewrite_tac [] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists `st` >> simp[]) >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  first_assum (irule_at Any) >> simp[]
QED

Finalise tuple_store_targets_path_ptr
