(* Equal-type store into the private snapshot allocation. *)
Theory bodyQualifiedSnapshotStoreEffectMods
Ancestors
  bodyAssignNameCopyStoreEffectMods contextProps fragGasOriginPtr
  valueEncodingProofs vyperTypeArgFits venomMemDefs valueCopyBytes
  context bodyDeclMemoryCore valueEncodingTyping words

Theorem qualified_snapshot_same_type_store_mods:
  compile_store_memory ce src (Var p) ty ty su = ((),sr) /\
  ~is_word_type ty /\ evaluate_type tenv ty = SOME rt /\
  cap = type_memory_size rt /\ type_memory_bytes ce ty = cap /\
  value_has_type rt v /\
  (0 < cap ==> ?x sw. src = Var x /\ not_fresh_at su x /\
    lookup_var x z = SOME sw /\ ptr_covers Gz tz x z cap /\
    w2n sw + val_store_size rt v <= z.vs_alloca_next /\
    (!m. mem_agree_outside tz.t_mem z.vs_memory m ==> val_in_memory rt v (w2n sw) m)) /\
  not_fresh_at su p /\ lookup_var p z = SOME (n2w b) /\
  ptr_covers Gz tz p z cap /\ FLOOKUP z.vs_allocas aid = SOME (b,cap) /\
  z.vs_alloca_next < dimword (:256) /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  alloca_history func z /\ alloca_inv z /\ fn_inst_ids_distinct func /\
  fn_has_code su sr func /\ ~z.vs_halted /\
  z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?n u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK u,Gu,tu)) /\
    n = val_store_size rt v /\ n <= cap /\
    (!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory rt v b m) /\
    typed_copy_state_frame su b n z u /\
    (!x. not_fresh_at su x ==> lookup_var x u = lookup_var x z /\
         FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)) /\
    tu.t_stor = tz.t_stor /\ tu.t_trans = tz.t_trans /\ tu.t_imm = tz.t_imm /\
    (!i. ~(b <= i /\ i < b + n) ==> (i IN tu.t_mem <=> i IN tz.t_mem)) /\
    ~u.vs_halted /\ u.vs_current_bb = sr.cs_current_bb /\
    u.vs_inst_idx = LENGTH sr.cs_current_insts /\ alloca_history func u
Proof
  strip_tac >> Cases_on `cap = 0`
  >- (`type_memory_size rt = 0 /\ type_memory_bytes ce ty = 0` by fs[] >>
      `~is_bytestring_type ty` by
        (strip_tac >> drule bytestring_memory_bytes_positive >>
         disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
      `sr = su` by fs[compile_store_memory_def,compile_copy_memory_zero] >>
      `val_store_size rt v = 0` by (drule_all val_store_size_non_bytestring >> simp[]) >>
      qexistsl_tac [`0`,`z`,`Gz`,`tz`] >>
      fs[gas_origin_ptr_path_rules,return_zero_wf_memory,value_has_type_val_wf]) >>
  `0 < cap` by decide_tac >>
  qpat_x_assum `0 < cap ==> _` (drule_then strip_assume_tac) >>
  `b + cap <= z.vs_alloca_next` by
    (qpat_assum `alloca_inv z` (strip_assume_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     first_x_assum drule >> simp[]) >>
  `w2n (n2w b : bytes32) = b` by (simp[] >> decide_tac) >>
  qpat_x_assum `cap = _` SUBST_ALL_TAC >>
  qpat_assum `w2n (n2w b : bytes32) = b` (once_rewrite_tac o single o SYM) >>
  irule (Q.INST [`sty` |-> `ty`, `tv` |-> `rt`] assign_name_copy_store_effect_mods) >>
  simp[] >>
  qpat_x_assum `src = Var x` SUBST_ALL_TAC >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  goal_assum (drule_at (Pat `lookup_var x z = _`)) >>
  qexists_tac `type_memory_size rt` >> simp[]
QED
