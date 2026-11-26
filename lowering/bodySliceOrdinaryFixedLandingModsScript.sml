(* Frame the fixed-byte staging allocation across the two ordinary Slice operands. *)
Theory bodySliceOrdinaryFixedLandingMods
Ancestors
  bodySliceFixedCaptureMods exprSimSliceOrdinaryFrame bodySliceOrdinaryFixedLayoutMods
  bodyFullPostsMods loweringPosts loweringStateRelDefs bodyPtrDefs
  compileEnv exprLoweringProps ptrDiscipline
  venomState arithmetic finite_map pred_set list rich_list byte words

Theorem slice_ordinary_fixed_landing_mods:
  stmt_state_rel H ctx func ce cx es t /\
  local_ptrs_reserved ce sb /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  FLOOKUP t.vs_allocas aid = SOME (b,32) /\
  aid < sb.cs_next_id /\
  aid < sc.cs_next_id /\
  LENGTH bs <= 32 /\
  (!name off sz. local_region ce es.scopes t name off sz ==>
                 b + 32 <= off \/ off + sz <= b) /\
  mem_bytes_at b (LENGTH bs) t.vs_memory = bs /\
  expr_post H ctx func ce cx start es sb sc t es1 v1 op1 t1 /\
  expr_post H ctx func ce cx len es1 sc sd t1 es2 v2 op2 u ==>
  mem_bytes_at b (LENGTH bs) u.vs_memory = bs
Proof
  metis_tac[slice_fixed_payload_two_operands]
QED
