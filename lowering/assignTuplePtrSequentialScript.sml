(* Memory-mode store composition abstracts over the per-target head contract.
   This boundary transports only unread resources, not the whole staged tuple. *)
Theory assignTuplePtrSequential
Ancestors
  assignTuplePtrLocalContract assignTuplePtrUnread assignTuplePtrUnreadBounds
  assignTuplePtrBoundary tupleTargetStoreProps tupleTargetStoreRun tupleLocalStoreRun
  tupleMemoryFrame bodyPtrDefs exprLoweringProps exprSimProps compileEnv
  venomState venomExecSemantics ptrDiscipline valueEncodingProps arithmetic
  stmtLowering vyperInterpreter fragGasPathPtr valueEncoding vyperTyping
  tupleAssignParts tupleMemoryLayout stmtLoweringMono fragExec stmtSimDefs
  freshWrites vyperState list rich_list finite_map

Theorem tuple_sequential_value_frame_ptr:
  ptr_val_ok cx ty v (Var p) G tn s /\
  lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
  op_taint tn' (Var p) = op_taint tn (Var p) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region cenv scopes s name b sz)) /\
  b <= addr /\
  (~is_word_type ty ==> !w. eval_operand (Var p) s = SOME w ==>
    addr + elem <= w2n w /\ w2n w + val_footprint tv v <= b + sz) /\
  ((t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem) \/
   ?id dst dsz written. local_region cenv scopes s id dst dsz /\
     written <= elem /\ written <= dsz /\
     (!i. ~(dst <= i /\ i < dst+written) ==>
       mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
       (i IN tn'.t_mem <=> i IN tn.t_mem))) ==>
  ptr_val_ok cx ty v (Var p) G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type ty` >- gvs[ptr_val_ok_def, op_prov_def] >>
  `eval_operand (Var p) t = eval_operand (Var p) s /\
   op_prov G' (Var p) = op_prov G (Var p)` by simp[eval_operand_def, op_prov_def] >>
  `!q. Var p = Var q ==> FLOOKUP G' q = FLOOKUP G q` by simp[] >>
  `!tv'. evaluate_type (get_tenv cx) ty = SOME tv' ==> val_wf tv' v` by simp[] >>
  qpat_x_assum `t.vs_memory = s.vs_memory /\ _ \/ _` strip_assume_tac
  >- gvs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
  drule_all tuple_container_write_position >> disch_tac >>
  `~is_word_type ty ==> !tv' w.
    evaluate_type (get_tenv cx) ty = SOME tv' /\ eval_operand (Var p) s = SOME w ==>
    addr + elem <= w2n w /\ w2n w + val_footprint tv' v <= b + sz` by simp[] >>
  drule_all tuple_unread_value_frame_ptr >> simp[]
QED

Theorem tuple_sequential_source_cons_ptr:
  assign_tuple_target_list cx (g::gs) (v::vs) es = (INL (),es') ==>
  ?es1. assign_tuple_targets cx g v es = (INL (),es1) /\
    assign_tuple_target_list cx gs vs es1 = (INL (),es')
Proof
  simp[Once vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  metis_tac[]
QED


Theorem tuple_store_sequential_path_ptr:
  !gs tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' G tn d D PG P.
    (!scopes scopes' g ty tv v.
      (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes') =
           OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n scopes)) /\
      P scopes g ty tv v ==> P scopes' g ty tv v) /\
    (!scopes g ty tv v. P scopes g ty tv v ==> ?bt. g = BaseTarget bt) /\
    (!g ty tv v ee ee'. P ee.scopes g ty tv v /\
      assign_tuple_targets cx g v ee = (INL (),ee') ==>
      MAP FDOM ee.scopes = MAP FDOM ee'.scopes /\
      (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n ee'.scopes) =
           OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n ee.scopes))) /\
    (!g ty tv v src sw sa sb ee ee' u H tt.
      compile_tuple_store_all cenv [ty] [g] [Var src] sa = ((),sb) /\
      assign_tuple_targets cx g v ee = (INL (),ee') /\ P ee.scopes g ty tv v /\
      value_has_type tv v /\ val_wf tv v /\ evaluate_type (get_tenv cx) ty = SOME tv /\
      local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
      (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
      (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
      lookup_var src u = SOME sw /\ (is_word_type ty ==> sw = typed_val_to_w256 tv v) /\
      (~is_word_type ty ==> ptr_covers H tt src u (type_memory_size tv)) /\
      ptr_val_ok cx ty v (Var src) H tt u /\ stmt_state_rel ctx func cenv cx ee u /\
      ghost_inv d cenv cx ee H tt u /\ fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
      u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t H' tt'. stmt_state_rel ctx func cenv cx ee' t /\ ghost_inv d cenv cx ee' H' tt' t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u /\
          FLOOKUP H' x = FLOOKUP H x /\ op_taint tt' (Var x) = op_taint tt (Var x)) /\
        (!aid bs. FLOOKUP u.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        ((t.vs_memory = u.vs_memory /\ tt'.t_mem = tt.t_mem) \/
         ?id dst dsz written. local_region cenv ee.scopes u id dst dsz /\
           written <= type_memory_size tv /\ written <= dsz /\
           (!i. ~(dst <= i /\ i < dst+written) ==>
             mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 u.vs_memory /\
             (i IN tt'.t_mem <=> i IN tt.t_mem))) /\
        gas_path_ptr D 0 ctx func PG H tt u 0 H' tt' (OK t)) /\
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (INL (),es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    EVERY (\op. ?x. op = Var x /\ not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    (!i. i < LENGTH gs ==>
      ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
      ?w. eval_operand (EL i ops) s = SOME w /\
        (if is_word_type (EL i tys) then w = typed_val_to_w256 (EL i tvs) (EL i vs)
         else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))) /\
        (!p. ~is_word_type (EL i tys) /\ EL i ops = Var p ==>
          ptr_covers G tn p s (type_memory_size (EL i tvs)))) /\
    (!i. i < LENGTH gs ==> P es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys ==> evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)) /\
    b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    fn_has_code st st' func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
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
      ntac 4 (pop_last_assum kall_tac) >>
      gvs[compile_tuple_store_all_def, comp_return_def,
          vyperInterpreterTheory.evaluate_def, return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' G tn d D PG P. _`
    (mk_asm "ih") >>
  qpat_x_assum `!scopes scopes' g ty tv v.
    (!n. OPTION_MAP _ (lookup_scopes n scopes') = _) /\ P scopes g ty tv v ==> _`
    (mk_asm "stable") >>
  qpat_x_assum `!scopes g ty tv v. P scopes g ty tv v ==> _` (mk_asm "base") >>
  qpat_x_assum `!g ty tv v ee ee'. P ee.scopes g ty tv v /\ _ ==> _` (mk_asm "source") >>
  qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt.
    compile_tuple_store_all _ _ _ _ _ = _ /\ _ ==> _` (mk_asm "callback") >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  `P es.scopes h ty tv v` by
    (qpat_assum `!i. i < LENGTH (h::gs) ==> P _ _ _ _ _`
      (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) []) >>
  `value_has_type tv v /\ val_wf tv v` by
    (asm_x "ih" kall_tac >> asm_x "callback" kall_tac >>
     fs[value_has_type_def, val_wf_def]) >>
  drule tuple_sequential_source_cons_ptr >> strip_tac >>
  asm "base" drule >> strip_tac >> gvs[] >>
  drule tuple_store_base_cons >> strip_tac >> suspend "head"
QED

Resume tuple_store_sequential_path_ptr[head]:
  markerLib.RESUME_TAC >>
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    (asm_x "ih" kall_tac >> asm_x "callback" kall_tac >> metis_tac[fn_has_code_split]) >>
  rename1 `compile_tuple_store_all cenv [ty] [BaseTarget bt] [Var src] st = ((),sm)` >>
  qpat_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `eval_operand (Var src) s = SOME sw` >>
  `lookup_var src s = SOME sw` by fs[eval_operand_def] >>
  `is_word_type ty ==> sw = typed_val_to_w256 tv v` by (strip_tac >> fs[]) >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by
    (qpat_assum `!i. i < _ ==> evaluate_type _ _ = _`
      (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) []) >>
  asm "callback" drule_all >>
  disch_then (qx_choose_then `t` (qx_choose_then `G'` (qx_choose_then `tn'`
    (map_every assume_tac o CONJUNCTS)))) >>
  asm "source" drule_all >> strip_tac >> suspend "tail"
QED

Resume tuple_store_sequential_path_ptr[tail]:
  markerLib.RESUME_TAC >>
  asm_x "ih" (drule_at (Pat `compile_tuple_store_all _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `assign_tuple_target_list _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`tvs1`, `addr + type_memory_size tv`, `b`, `sz`] mp_tac) >>
  asm "callback" assume_tac >>
  disch_then (drule_at (Pos (el 4))) >>
  (impl_tac >- suspend "premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >> suspend "compose"
QED

Resume tuple_store_sequential_path_ptr[premises]:
  markerLib.RESUME_TAC >> (rpt conj_tac
  >- (asm "stable" ACCEPT_TAC)
  >- (asm "base" ACCEPT_TAC)
  >- (asm "source" ACCEPT_TAC)
  >- fs[] >- fs[] >- fs[] >- fs[]
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!op. MEM op ops1 ==> _` drule >> strip_tac >> gvs[] >>
      irule not_fresh_at_mono >> qexists `st` >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[])
  >- fs[value_has_type_def]
  >- fs[val_wf_def]
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `st` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `st` >> simp[])
  >- suspend "resources"
  >- (gen_tac >> strip_tac >> asm "stable" irule >>
      qexists `es.scopes` >> simp[] >>
      qpat_x_assum `!i. i < _ ==> P _ _ _ _ _`
        (qspec_then `SUC i` mp_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < _ ==> evaluate_type _ _ = _`
        (qspec_then `SUC i` mp_tac) >> simp[])
  >- fs[] >- fs[type_memory_size_def]
  >- (irule tuple_container_transport >>
      qexistsl_tac [`s`, `st`, `es.scopes`] >> simp[] >>
      asm_x "callback" kall_tac >>
      qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt. _` kall_tac >>
      metis_tac[])
  >> asm_rewrite_tac [])
QED

Resume tuple_store_sequential_path_ptr[resources]:
  markerLib.RESUME_TAC >> (
  gen_tac >> strip_tac >>
  `i < LENGTH ops1 /\ i < LENGTH tys1 /\ i < LENGTH tvs1` by fs[] >>
  `?p. EL i ops1 = Var p /\ not_fresh_at st p` by
    (asm_x "callback" kall_tac >>
     qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt. _` kall_tac >>
     fs[EVERY_EL] >> metis_tac[]) >>
  qpat_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp_tac (srw_ss()) [] >>
  (impl_tac >- fs[]) >> strip_tac >>
  rename1 `eval_operand (EL i ops1) s = SOME w` >>
  `lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
   op_taint tn' (Var p) = op_taint tn (Var p)` by
    (asm_x "callback" kall_tac >>
     qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt. _` kall_tac >> metis_tac[]) >>
  `eval_operand (Var p) t = SOME w /\
   op_prov G' (Var p) = op_prov G (Var p)` by
    gvs[eval_operand_def, op_prov_def] >>
  `ptr_val_ok cx (EL i tys1) (EL i vs1) (Var p) G' tn' t` by suspend "robust" >>
  conj_tac >- gvs[] >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  asm_x "callback" kall_tac >>
  qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt. _` kall_tac >>
  gvs[ptr_covers_def])
QED

Resume tuple_store_sequential_path_ptr[robust]:
  markerLib.RESUME_TAC >> (
  asm_x "callback" kall_tac >>
  qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt. _` kall_tac >>
  Cases_on `is_word_type (EL i tys1)`
  >- gvs[ptr_val_ok_def, op_prov_def] >>
  `evaluate_type (get_tenv cx) (EL i tys1) = SOME (EL i tvs1)` by
    (qpat_assum `!i. i < _ ==> evaluate_type _ _ = _`
      (qspec_then `SUC i` mp_tac) >> simp_tac (srw_ss()) [] >> fs[]) >>
  `values_have_types tvs1 vs1` by fs[value_has_type_def] >>
  `val_wf (EL i tvs1) (EL i vs1) /\
   addr + type_memory_size tv <= w2n w /\
   w2n w + val_footprint (EL i tvs1) (EL i vs1) <= b + sz` by
    (irule tuple_unread_element_resources_ptr >> simp[] >>
     qpat_x_assum `if is_word_type (EL i tys1) then _ else _` mp_tac >>
     simp[] >> decide_tac) >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  irule tuple_sequential_value_frame_ptr >>
  qexistsl_tac [`G`, `addr`, `b`, `cenv`, `type_memory_size tv`, `func`,
    `s`, `es.scopes`, `sz`, `tn`, `EL i tvs1`] >>
  asm_x "stable" kall_tac >> asm_x "base" kall_tac >> asm_x "source" kall_tac >>
  qpat_x_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _` kall_tac >>
  qpat_x_assum `!i. i < _ ==> P _ _ _ _ _` kall_tac >>
  simp[eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[eval_operand_def]) >>
  conj_tac >- metis_tac[] >> gvs[])
QED

Resume tuple_store_sequential_path_ptr[compose]:
  markerLib.RESUME_TAC >> (
  asm_x "callback" kall_tac >>
  qpat_x_assum `!g ty tv v src sw sa sb ee ee' u H tt. _` kall_tac >>
  asm_x "stable" kall_tac >> asm_x "base" kall_tac >> asm_x "source" kall_tac >>
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
  first_assum (irule_at Any) >> simp[])

QED

Finalise tuple_store_sequential_path_ptr
