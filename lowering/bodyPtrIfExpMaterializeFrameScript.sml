Theory bodyPtrIfExpMaterializeFrame
Ancestors
  bodyPtrIfExpMaterializeWord bodyPtrIfExpAllocSeparation
  bodyPtrIfExpBytesCallerFrame ptrDiscipline pred_set finite_map
  bodyPtrDefs loweringPosts compileEnv venomState venomInst words
  exprSimDefs valueEncoding loweringHalt

Theorem ifexp_key_taint_bound:
  key_taint X key SUBSET count 32
Proof
  simp[key_taint_def, SUBSET_DEF]
QED

Theorem ifexp_materialize_load_taint_bound:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a ==>
  op_taint (step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn)
    (Var out) SUBSET count 32
Proof
  strip_tac >> drule_all ifexp_materialize_load_taint >> strip_tac >>
  simp[op_taint_def, FLOOKUP_UPDATE] >>
  rpt IF_CASES_TAC >> simp[ifexp_key_taint_bound]
QED

Theorem ifexp_interior_region_separate:
  off+sz <= b \/ b+capacity <= off ==>
  j+n <= capacity ==> off+sz <= b+j \/ b+j+n <= off
Proof
  decide_tac
QED

Theorem ifexp_alloca_interior_original_site:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) (fn_insts fn) /\
  sa.cs_next_id <= sb.cs_next_id /\ capacity < dimword(:256) /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  b = buffer_allocation_base s sb.cs_next_id /\ j+n <= capacity ==>
  off+sz <= b+j \/ b+j+n <= off
Proof
  strip_tac >> drule_all ifexp_alloca_original_site_separate >>
  strip_tac >> decide_tac
QED

Theorem ifexp_alloca_interior_original_local:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) (fn_insts fn) /\
  not_local_ptr ce ee.scopes out /\ capacity < dimword(:256) /\
  local_region ce es.scopes s0 name p sz /\
  b = buffer_allocation_base s sb.cs_next_id /\ j+n <= capacity ==>
  p+sz <= b+j \/ b+j+n <= p
Proof
  strip_tac >> drule_all ifexp_alloca_original_local_separate >>
  strip_tac >> decide_tac
QED

Theorem ifexp_interior_live_local_bounds:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sc s0 ee raw vv t /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  j+n <= capacity /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+capacity <= p) ==>
  !name entry p sz w.
    lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= b+j \/ b+j+n <= w2n w)
Proof
  strip_tac >> drule ifexp_bytes_live_local_frame_bounds >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`capacity`,`capacity`,`b`] mp_tac) >>
  simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\
   (w2n w+type_memory_size entry.type <= b \/ b+capacity <= w2n w)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[] >> decide_tac
QED
