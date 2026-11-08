(* Physical restriction of tuple layouts, independent of expression execution. *)
Theory bodyPtrSubscriptSeamTupleMemory
Ancestors
  bodyPtrSubscriptTupleLayout exprSimTuple exprSimFieldLayout
  loweringPosts exprSimHyps valueEncoding valueEncodingProofs
  tupleMemoryLayout vyperInterpreter vyperValueOperation context
  exprSimDefs exprLowering compileEnv venomState vyperAST exprSimAttributeProps exprSimProps exprSimAttributeFields
  list rich_list

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
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs ==>
  vv_at cenv cx ct sa sn es1 tv'
    (LocatedValue t (mk_ptr dst (vv_loc bvv))) q
Proof
  strip_tac >> gvs[] >>
  simp[vv_at_def, mk_ptr_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >> simp[]) >>
  gvs[] >> drule_all tuple_memory_child_address >> strip_tac >>
  drule_all tuple_memory_placement >> strip_tac >>
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
      drule_all local_path_at_step >>
      `w2n w - b + SUM (TAKE k (MAP type_memory_size tvs)) =
       w2n w + SUM (TAKE k (MAP type_memory_size tvs)) - b` by decide_tac >>
      simp[local_path_at_val_at] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED
