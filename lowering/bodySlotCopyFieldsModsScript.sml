(* The normalized slot fold and linked ghost frame at its actual endpoint. *)
Theory bodySlotCopyFieldsMods
Ancestors
  stmtSimStoreCopy bodyFullShadowBodyInv bodyPtrDefs loweringStateRelDefs
  ptrDiscipline venomState finite_map list

Theorem slot_copy_fold_fields[local]:
  !(ks:num list) u.
    (FOLDL (\q j. (if tr then tstore else sstore) (key j) (rd j) q) u ks).vs_data_section =
    u.vs_data_section /\
    (FOLDL (\q j. (if tr then tstore else sstore) (key j) (rd j) q) u ks).vs_immutables =
    u.vs_immutables
Proof
  Induct >> simp[FOLDL] >> Cases_on `tr` >> simp[tstore_def,sstore_def]
QED

Theorem slot_copy_normalized_fields:
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (key j) (rd j) q) s (ks:num list) ==>
  t.vs_data_section = s.vs_data_section /\ t.vs_immutables = s.vs_immutables
Proof
  disch_then (mp_tac o GSYM) >>
  disch_then (fn th => mp_tac (Q.SPECL [`ks`,`s`] slot_copy_fold_fields) >>
                       rewrite_tac[th,store_copy_normalize_def]) >>
  simp[]
QED

Theorem slot_copy_ghost_frame_mods:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
  ef.scopes = ee.scopes /\ t.vs_memory = s.vs_memory /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  tnf.t_mem = tn.t_mem /\ stor_taint_ok_at D tnf t ==>
  ghost_inv_at_mods D lo d cenv cx ef Gf tnf t
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
           ptr_covers Gf tnf p t sz` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` drule >>
     simp[ptr_covers_def] >> fs[ptr_covers_def]) >>
  fs[ghost_inv_at_mods_def,allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      qpat_assum `!x. not_fresh_at sa x ==> _` drule >>
      strip_tac >> simp[] >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED
