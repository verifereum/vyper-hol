(* Compatible local targets instantiate the execution-only sequence kernel.
   Compiler openness is deliberately a separate property. *)
Theory assignTuplePtrLocalSequence
Ancestors
  assignTuplePtrSequential assignTuplePtrLocalContract assignTuplePtrLocalSourceFrame
  tupleTargetStoreProps bodyPtrDefs stmtSimDefs stmtLowering context compileEnv
  vyperInterpreter vyperState vyperLookup venomState venomExecSemantics
  ptrDiscipline valueEncoding valueEncodingProps vyperTyping list finite_map

Theorem tuple_local_store_sequence_path_ptr:
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
  (!i. i < LENGTH gs ==>
    ?id p sz vt entry. EL i gs = BaseTarget (NameTarget id) /\
      lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
      (is_word_type vt = is_word_type (EL i tys)) /\
      (if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs) else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type (EL i vs) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        type_memory_bytes cenv vt = type_memory_size entry.type /\
        0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))) /\
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
  strip_tac >>
  irule tuple_store_sequential_path_ptr >> simp[] >>
  qexists `\scopes g ty tv v.
    ?id p sz vt entry. g = BaseTarget (NameTarget id) /\
      lookup_scopes id scopes = SOME entry /\ entry.assignable /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
      (is_word_type vt = is_word_type ty) /\
      (if is_word_type ty then store_lays_out tv entry.type v else
        (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type v /\
        type_memory_bytes cenv ty = type_memory_size tv /\
        type_memory_bytes cenv vt = type_memory_size entry.type /\
        0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))` >>
  qexistsl_tac [`addr`, `b`, `es`, `gs`, `ops`, `sz`, `tvs`, `tys`, `vs`] >>
  simp[] >>
  (rpt conj_tac
   >- (rpt gen_tac >> strip_tac >> gvs[] >>
       drule tuple_local_assignment_scope_frame_ptr >> simp[])
   >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
       drule_all tuple_local_compatibility_callback_ptr >> simp[])
   >- (rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[])
   >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
       drule_all tuple_local_compatibility_scope_ptr >> simp[])
   >> metis_tac[])
QED
