(* Degenerate physical slot copies. Source writes still test cx.txn.is_static
   and encode the declared type, independently of this machine split. *)
Theory bodySlotCopyLimitsMods
Ancestors
  bodyFullStoreSlotsStatic bodyFullStoreSlotsPath stmtSimStoreCopy
  bodyFullPathHistory bodyPtrDefs placeStoreStorage vyperStorageBackend
  vyperEncodeDecode vyperStorage vyperState vyperTypeSystem list pred_set
  venomExecSemantics venomState

Theorem slot_copy_zero_encoding[local]:
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  type_slot_size tv = 0 ==> writes = []
Proof
  Cases_on `writes` >- simp[] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!i. MEM i (MAP FST (h::t)) ==> i < type_slot_size tv` by
    metis_tac[cj 1 encode_writes_bounded] >>
  pop_assum (qspec_then `FST h` mp_tac) >> simp[]
QED

Theorem slot_copy_no_write_fields[local]:
  store_copy_normalize s t = s ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
  t.vs_fmp = s.vs_fmp
Proof
  simp[store_copy_normalize_def, venom_state_component_equality]
QED

Theorem slot_copy_static_or_zero_mods:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
                              sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_call_ctx.cc_static \/ type_slot_size tv = 0) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      ((if type_slot_size tv = 0 then OK t
        else Abort ExHalt_abort (halt_state (set_returndata [] t))),Gf,tnf)) /\
    store_copy_normalize s t = s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    (if tr then tnf.t_trans else tnf.t_stor) SUBSET
      (if tr then tn.t_trans else tn.t_stor) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
    ~t.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!D. stor_taint_ok_at D tn s ==> stor_taint_ok_at D tnf t) /\
    (type_slot_size tv = 0 ==>
      writes = [] /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (alloca_history func s /\ alloca_inv s ==> alloca_history func t)) /\
    (type_slot_size tv <> 0 ==>
      s.vs_call_ctx.cc_static /\
      ?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst /\
        inst.inst_opcode = (if tr then TSTORE else SSTORE) /\
        step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `(type_slot_size tv = 0 ==> writes = [])` by
    (strip_tac >> drule_all_then ACCEPT_TAC slot_copy_zero_encoding) >>
  Cases_on `s.vs_call_ctx.cc_static`
  >- (mp_tac (SPEC_ALL compile_store_slots_static_origin_ptr_path) >>
      (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >>
      disch_then (qx_choosel_then [`t`,`Gf`,`tnf`]
        (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
      `!D. stor_taint_ok_at D tn s ==> stor_taint_ok_at D tnf t` by
        (drule slot_copy_no_write_fields >> simp[stor_taint_ok_at_def]) >>
      suspend "finish") >>
  mp_tac (SPEC_ALL compile_store_slots_origin_ptr_path) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choosel_then [`t`,`ks`,`Gf`,`tnf`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `type_slot_size tv = 0` by fs[] >>
  `writes = []` by simp[] >>
  `ks = []` by
    (Cases_on `ks` >> simp[] >>
     qpat_x_assum `!j. MEM j (_::_) <=> _` (qspec_then `h` mp_tac) >> simp[]) >>
  `store_copy_normalize s t = s` by fs[] >>
  qpat_x_assum `_ SUBSET FOLDL _ _ _` mp_tac >>
  simp[] >> disch_tac >>
  `!D. stor_taint_ok_at D tn s ==> stor_taint_ok_at D tnf t` by
    (drule slot_copy_no_write_fields >> strip_tac >>
     Cases_on `tr` >> fs[stor_taint_ok_at_def] >> metis_tac[SUBSET_TRANS]) >>
  suspend "finish"
QED

Resume slot_copy_static_or_zero_mods[finish]:
  markerLib.RESUME_TAC >>
  drule slot_copy_no_write_fields >> strip_tac >>
  drule bodyFullStoreSlotsFrameTheory.store_slots_normalize_allocas_below_fmp >> strip_tac >>
  `(type_slot_size tv = 0 /\ alloca_history func s /\ alloca_inv s) ==>
    alloca_history func t` by
    (strip_tac >>
     `gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
       (qpat_x_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) _ _ _`
          (qspec_then `ARB:dead` mp_tac) >> simp[]) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[SF CONJ_ss]
QED
Finalise slot_copy_static_or_zero_mods

Theorem slot_copy_source_static_or_zero_mods:
  (cx.txn.is_static \/ encode_value dtv v = SOME []) ==>
  write_storage_slot cx tr dw dtv v ee =
    (if cx.txn.is_static then INR (Error (RuntimeError "write in static context"))
     else INL (),ee)
Proof
  Cases_on `cx.txn.is_static` >> simp[write_storage_slot_eq,apply_writes_def] >>
  Cases_on `tr` >> simp[set_storage_def,get_storage_def,place_store_update_identity]
QED
