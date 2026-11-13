(* Captured values, not the original source place, survive effectful targets.
   The layout tv may be the lowered layout rather than the RHS annotation.
   Operand labels are excluded: the compiler's saved values are literals or
   variables, whereas target_post intentionally does not frame label tables. *)
Theory bodyMemSnapshotTargetFrame
Ancestors
  loweringPosts exprSimProps exprBopSimProps valueEncodingProofs
  exprLoweringProps loweringStateRelDefs freshWrites venomMemDefs

Theorem snapshot_target_operand_frame:
  target_post ctx func ce cx es sa sb s0 ee pv vt r z /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!l. op <> Label l) /\ eval_operand op s0 = SOME w /\
  sa.cs_next_var <= sb.cs_next_var ==>
  eval_operand op z = SOME w /\
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> conj_tac
  >- (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `s0`] >>
      gvs[target_post_def]) >>
  metis_tac[not_fresh_at_mono]
QED

(* The whole containing allocation is framed, hence any captured value
   fitting in it retains its encoding, including its dynamically-sized tail.
   Retaining the entry also retains room up to the endpoint's alloca cursor. *)
Theorem snapshot_target_owned_memory_frame:
  target_post ctx func ce cx es sa sb s0 ee pv vt r z /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!l. op <> Label l) /\ eval_operand op s0 = SOME w /\
  sa.cs_next_var <= sb.cs_next_var /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
     b + sz <= lb \/ lb + len <= b) /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s0.vs_memory ==>
  eval_operand op z = SOME w /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
  b + sz <= z.vs_alloca_next /\
  w2n w + val_footprint tv v <= z.vs_alloca_next /\
  mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz s0.vs_memory /\
  val_in_memory tv v (w2n w) z.vs_memory
Proof
  strip_tac >>
  drule_all snapshot_target_operand_frame >> strip_tac >>
  `FLOOKUP z.vs_allocas aid = SOME (b,sz)` by
    (fs[target_post_def] >> metis_tac[]) >>
  `b + sz <= z.vs_alloca_next` by
    (fs[target_post_def, stmt_state_rel_def,
        alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz s0.vs_memory` by
    (fs[target_post_def] >> metis_tac[]) >>
  simp[] >>
  irule val_in_memory_footprint_agree >> simp[] >> qexists_tac `s0.vs_memory` >>
  simp[] >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
  strip_tac >> metis_tac[]
QED

Theorem snapshot_target_scalar_frame:
  target_post ctx func ce cx es sa sb s0 ee pv vt r z /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  sa.cs_next_var <= sb.cs_next_var /\
  is_word_type ty /\ expr_val_rel cx ty v op s0 ==>
  expr_val_rel cx ty v op z /\
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> fs[expr_val_rel_def] >>
  drule_all snapshot_target_operand_frame >> strip_tac >>
  simp[expr_val_rel_def] >> metis_tac[]
QED

(* Ownership's local-separation clause survives too.  Scope-domain equality
   is a source target-evaluation fact, not a purity assumption. *)
Theorem snapshot_target_local_separation:
  target_post ctx func ce cx es sa sb s0 ee pv vt r z /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
     b + sz <= lb \/ lb + len <= b) ==>
  (!n lb len. local_region ce ee.scopes z n lb len ==>
     b + sz <= lb \/ lb + len <= b)
Proof
  rpt strip_tac >>
  `local_region ce es.scopes s0 n lb len` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `z`] >> gvs[target_post_def]) >>
  metis_tac[]
QED
