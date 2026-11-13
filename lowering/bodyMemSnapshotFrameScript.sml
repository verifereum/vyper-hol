(* Ambient postconditions across a store confined to a fresh allocation. *)
Theory bodyMemSnapshotFrame
Ancestors
  exprSimCopy exprSimStorageCopy exprSimProps loweringPosts loweringStateRelDefs freshWrites
  exprLoweringProps compileEnv context

Theorem snapshot_store_post_frame:
  expr_post ctx func ce cx e es sa sc s0 ee v src s /\
  post_value_type ce e = expr_type e /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  copy_static z = copy_static s /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\ sm.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!n lb len. local_region ce ee.scopes s n lb len ==>
     regions_disjoint b sz lb len) /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
     aid < sa.cs_next_id ==> regions_disjoint b sz off len) /\
  (!off len. off + len <= b \/ b + sz <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  vv_holds ce cx (expr_type e) raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) ee z /\
  vv_at ce cx (expr_type e) sa sb ee raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z ==>
  vv_post ctx func ce cx e es sa sb s0 ee raw
    (LocatedValue lt <|ptr_location := LocMemory; ptr_operand := dst|>) z /\
  pure_frame ce func ee sm s z
Proof
  strip_tac >>
  `!n lb len. local_region ce es.scopes s0 n lb len ==>
     regions_disjoint b sz lb len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s n lb len` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> gvs[expr_post_def]) >>
     metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >>
     gvs[expr_post_def, regions_disjoint_def] >> metis_tac[]) >>
  `locals_kept ce es ee s0 z` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl_tac [`b`, `s`, `sz`] >>
     gvs[expr_post_def, regions_disjoint_def] >> metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 z` by
    (strip_tac >> irule pure_frame_buffer_tail >>
     qexistsl_tac [`b`, `sz`, `inst`, `s`] >>
     gvs[expr_post_def, regions_disjoint_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (irule pure_frame_buffer_tail >>
      qexistsl_tac [`b`, `sz`, `inst`, `s`] >>
      simp[regions_disjoint_def] >>
      metis_tac[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  simp[vv_post_def] >>
  gvs[expr_post_def] >>
  simp[] >> rpt strip_tac >>
  rename1 `FLOOKUP s0.vs_allocas aid = SOME (off,len)` >>
  `regions_disjoint b sz off len` by metis_tac[] >>
  `mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ s.vs_memory = _` drule >>
  simp[] >> (impl_tac >- (rpt strip_tac >>
    qpat_x_assum `!n b sz'. local_region _ _ _ _ _ _ ==> _` drule >>
    simp[arithmeticTheory.ADD_COMM])) >> simp[]
QED
