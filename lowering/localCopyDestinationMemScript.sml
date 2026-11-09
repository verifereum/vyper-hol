(* Destination backing and address bounds for typed local copies. *)
Theory localCopyDestinationMem
Ancestors
  bodyMemAssignTupleLocalsFacts stagedLocalRegionCopyMem compileEnv
  exprLoweringProps venomMemDefs words arithmetic

Theorem local_copy_destination_region:
  stmt_state_rel ctx fn ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ n <= type_memory_size entry.type ==>
  local_region ce es.scopes s id (w2n w) sz /\
  n <= sz /\ w2n w + n <= s.vs_alloca_next /\
  w2n w + n < dimword(:256)
Proof
  strip_tac >> drule_all tuple_local_destination_room >> strip_tac >>
  `s.vs_alloca_next < dimword(:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `local_region ce es.scopes s id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  simp[] >> decide_tac
QED

(* A declaration's pointer is not in the scopes yet; its recorded allocation
   supplies the same extent bounds without claiming a live local region. *)
Theorem allocated_copy_destination_extent:
  stmt_state_rel ctx fn ce cx es s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ n <= sz ==>
  b + n <= s.vs_alloca_next /\ b + n < dimword(:256)
Proof
  strip_tac >>
  `alloca_next_valid s /\ alloca_room ctx fn s` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `b + sz <= s.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
  drule alloca_room_next_lt >> decide_tac
QED
