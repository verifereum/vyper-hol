(* Physical restriction of tuple layouts, independent of expression execution. *)
Theory bodyPtrSubscriptSeamTupleMemory
Ancestors
  bodyPtrSubscriptTupleLayout exprSimTuple exprSimFieldLayout
  loweringPosts exprSimHyps valueEncoding valueEncodingDefs valueEncodingProofs
  tupleMemoryLayout vyperInterpreter vyperValueOperation context
  exprSimDefs exprLowering compileEnv venomState vyperAST exprSimAttributeProps exprSimProps exprSimAttributeFields
  list rich_list bodyPtrAttributeFields typedCopyLayoutPtr bodyPtrDefs

Theorem tuple_child_sub_layout:
  sub_layout itv iv start (TupleTV tvs) (ArrayV (TupleV vs)) /\
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs ==>
  sub_layout itv iv (start + SUM (MAP type_memory_size (TAKE k tvs)))
    (EL k tvs) (EL k vs)
Proof
  rw[sub_layout_def]
  >- (drule tuple_element_interval >>
      gvs[type_memory_size_def, type_memory_size_list_sum] >> decide_tac) >>
  first_x_assum drule >> simp[val_in_memory_def] >> strip_tac >>
  drule_all tuple_in_memory_element >> metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem tuple_memory_placement:
  vv_at cenv cx (TupleT tys) sa sb es tv vv s /\
  read_result cx tv es = (INL (ArrayV (TupleV vs)),es) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
  tuple_val_wf vs tvs /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
     b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
     (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\
     b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
     local_path_at cenv cx n (w2n w - b) (TupleTV tvs)) \/
   type_memory_size_list tvs = 0)
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, local_val_at_def, is_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[val_wf_def, val_footprint_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem tuple_child_wf:
  !vs tvs k. tuple_val_wf vs tvs /\ LENGTH vs = LENGTH tvs /\
    k < LENGTH tvs ==> val_wf (EL k tvs) (EL k vs)
Proof
  Induct >> Cases_on `tvs` >> simp[val_wf_def] >>
  rpt gen_tac >> Cases_on `k` >> gvs[val_wf_def]
QED

Theorem tuple_memory_child_address:
  stmt_state_rel ctx func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
  vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
  read_result cx tv es1 = (INL (ArrayV (TupleV vs)),es1) /\
  eval_operand (vv_operand bvv) q = SOME w /\ vv_loc bvv = LocMemory /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs ==>
  tuple_offset cenv tys LocMemory k = SUM (TAKE k (MAP type_memory_size tvs)) /\
  tuple_offset cenv tys LocMemory k + type_memory_size (EL k tvs) <=
    type_memory_size_list tvs /\
  w2n (w + n2w (tuple_offset cenv tys LocMemory k)) =
    w2n w + tuple_offset cenv tys LocMemory k
Proof
  strip_tac >> drule_all tuple_memory_sizes >> strip_tac >>
  drule_all tuple_memory_placement >> strip_tac >>
  `SUM (TAKE k (MAP type_memory_size tvs)) + type_memory_size (EL k tvs) <=
    type_memory_size_list tvs` by
    (drule tuple_element_interval >>
     gvs[MAP_TAKE, type_memory_size_list_sum] >> decide_tac) >>
  `tuple_offset cenv tys LocMemory k = SUM (TAKE k (MAP type_memory_size tvs))` by
    simp[tuple_offset_def] >>
  simp[] >> drule stmt_state_rel_region_lt >> strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule field_ptr_w2n >>
  qexistsl_tac [`type_memory_size (EL k tvs)`, `type_memory_size_list tvs`] >>
  simp[] >>
  first_x_assum drule_all >> strip_tac >> decide_tac
QED

(* vv_at's memory placement of a non-word base, with the local place pin;
   as exprSimTuple's base_vv_at_mem. *)
Theorem tuple_base_vv_at_mem[local]:
  !cenv cx t sa sb es tv vv s v tvt w.
    vv_at cenv cx t sa sb es tv vv s /\ ~is_word_type t /\
    read_result cx tv es = (INL v, es) /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    (!bt. tvt <> BaseTV bt) /\
    vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
    val_wf tvt v /\
    ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                 sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                 b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                 (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                              b + sz <= lb \/ lb + lsz <= b)) \/
     (?n b sz. local_region cenv es.scopes s n b sz /\
               b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
               local_path_at cenv cx n (w2n w - b) tvt /\
               local_place_at cenv cx n (w2n w - b) tvt tv) \/
     val_footprint tvt v = 0)
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, local_val_at_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  gvs[local_place_at_def] >> metis_tac[]
QED

Theorem tuple_child_placement:
  stmt_state_rel ctx func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
  vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
  read_result cx tv es1 = (INL (ArrayV (TupleV vs)),es1) /\
  read_result cx tv' es1 = (INL (EL k vs),es1) /\
  eval_operand (vv_operand bvv) q = SOME w /\
  eval_operand dst q = SOME (w + n2w off) /\
  off = tuple_offset cenv tys (vv_loc bvv) k /\ ct = EL k tys /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
  (!id path'. tv' = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV &k)] /\ tv = PlaceR (MemoryPlace id path)) ==>
  vv_at cenv cx ct sa sn es1 tv'
    (LocatedValue t (mk_ptr dst (vv_loc bvv))) q
Proof
  strip_tac >> gvs[] >>
  simp[vv_at_def, mk_ptr_def] >> conj_tac
  >- (rpt strip_tac >>
      `?p0. tv = PlaceR (MemoryPlace id p0)` by metis_tac[] >>
      qpat_x_assum `vv_at _ _ (TupleT _) _ _ _ _ _ _` mp_tac >>
      Cases_on `bvv` >>
      gvs[vv_at_def, vv_loc_def, vv_location_def, is_word_type_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >> simp[]) >>
  gvs[] >> drule_all tuple_memory_child_address >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `TupleT tys`, `sa`, `sn`, `es1`, `tv`, `bvv`,
               `q`, `ArrayV (TupleV vs)`, `TupleTV tvs`, `w`] mp_tac
    tuple_base_vv_at_mem >>
  impl_tac >- simp[is_word_type_def] >>
  disch_then (strip_assume_tac o
    SIMP_RULE (srw_ss()) [val_footprint_def, type_memory_size_def, val_wf_def]) >>
  `val_wf (EL k tvs) (EL k vs)` by (irule tuple_child_wf >> simp[]) >>
  `val_footprint (EL k tvs) (EL k vs) <= type_memory_size (EL k tvs)` by
    simp[val_footprint_le] >>
  simp[]
  >~ [`FLOOKUP q.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv es1.scopes q n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[] >>
      `mem_step_offset (TupleTV tvs) (ValueSubscript (IntV (&k))) =
       SOME (SUM (TAKE k (MAP type_memory_size tvs)),EL k tvs)` by
        simp[mem_step_offset_def, type_memory_size_list_sum, MAP_TAKE] >>
      `local_place_at cenv cx n
         (w2n w - b + SUM (TAKE k (MAP type_memory_size tvs))) (EL k tvs) tv'` by
        (irule local_place_at_step >> metis_tac[]) >>
      drule_all local_path_at_step >>
      `w2n w - b + SUM (TAKE k (MAP type_memory_size tvs)) =
       w2n w + SUM (TAKE k (MAP type_memory_size tvs)) - b` by decide_tac >>
      gvs[local_path_at_val_at] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

(* Extract robust contents for either a stack aggregate or a memory place. *)
Theorem nonword_memory_ptr_contents:
  ~is_word_type ty /\ ptr_vv_ok cx ty tv vv ee G tn s /\
  read_result cx tv ee = (INL v,ee) /\ vv_loc vv = LocMemory ==>
  ptr_mem_ok cx ty v (vv_operand vv) G tn s
Proof
  Cases_on `vv` >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, vv_operand_def,
       vv_loc_def, vv_location_def] >> rpt strip_tac >> gvs[]
QED

Theorem tuple_memory_selected_ptr:
  ptr_vv_ok cx (TupleT tys) tv vv ee G tn s /\ vv_loc vv = LocMemory /\
  ptr_buf_ok cenv obj (vv_operand vv) G s /\
  read_result cx tv ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx tv' ee = (INL (EL k vs),ee) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) ct = SOME (EL k tvs) /\
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\ tuple_val_wf vs tvs /\
  type_memory_bytes cenv (lowered_value_type cenv obj) = type_memory_size_list tvs /\
  type_memory_bytes cenv (lowered_value_type cenv child) = type_memory_size (EL k tvs) /\
  off = SUM (MAP type_memory_size (TAKE k tvs)) /\
  eval_operand (vv_operand vv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w off) /\
  w2n (w + n2w off) = w2n w + off /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\ op_taint tn' dst = {} /\
  (!x b sz. vv_operand vv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
    ?y. dst = Var y /\ FLOOKUP H y = SOME (b,sz)) ==>
  ptr_vv_ok cx ct tv' (LocatedValue ann (mk_ptr dst LocMemory)) ee H tn' t /\
  ptr_buf_ok cenv child dst H t
Proof
  strip_tac >>
  `ptr_mem_ok cx (TupleT tys) (ArrayV (TupleV vs)) (vv_operand vv) G tn s` by
    (irule nonword_memory_ptr_contents >> simp[is_word_type_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `off + type_memory_size (EL k tvs) <= type_memory_size_list tvs` by
    (drule tuple_element_interval >> simp[type_memory_size_list_sum] >> gvs[]) >>
  `ptr_buf_ok cenv child dst H t` by
    (irule ptr_buf_ok_offset >>
     qexistsl_tac [`G`, `obj`, `off`, `s`, `vv_operand vv`, `w`] >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `val_wf (EL k tvs) (EL k vs)` by
    (irule tuple_child_wf >> simp[]) >>
  simp[] >> irule ptr_vv_ok_memory >> simp[mk_ptr_def] >>
  irule ptr_mem_ok_of_buffer >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `child`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`TupleTV tvs`, `w`] mp_tac) >>
  simp[valueEncodingDefsTheory.val_in_memory_def] >> strip_tac >>
  drule_all tuple_in_memory_robust_element >> simp[]
QED
