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

