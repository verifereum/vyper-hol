(* Physical restriction of tuple layouts, independent of expression execution. *)
Theory bodyPtrSubscriptSeamTupleMemory
Ancestors
  bodyPtrSubscriptTupleLayout exprSimTuple exprSimFieldLayout
  loweringPosts exprSimHyps valueEncoding valueEncodingProofs
  tupleMemoryLayout vyperInterpreter vyperValueOperation context
  exprSimDefs exprLowering compileEnv venomState vyperAST exprSimAttributeProps
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
