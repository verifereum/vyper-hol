(* Actual-footprint transport from full old-allocation and local frames. *)
Theory bodyIntCallFamCallIntFootprintFrame
Ancestors
  bodyIntCallFamCallIntTransport valueEncodingProps loweringPosts context
  finite_map words

Theorem intcall_contained_bytes_frame:
  mem_bytes_at lb len m = mem_bytes_at lb len m' /\
  lb <= off /\ off + sz <= lb + len ==>
  mem_bytes_at off sz m = mem_bytes_at off sz m'
Proof
  strip_tac >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`off-lb`, `sz`] mp_tac) >> simp[]
QED

Theorem intcall_vv_at_footprint_frame:
  vv_at ce cx ty a b es r vv s /\ b.cs_next_id <= sa.cs_next_id /\
  (!aid lb len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (lb,len) ==>
    mem_bytes_at lb len u.vs_memory = mem_bytes_at lb len s.vs_memory) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    mem_bytes_at lb len u.vs_memory = mem_bytes_at lb len s.vs_memory) ==>
  (case vv of
     StackValue ann op => (~is_word_type ty ==> !v tv w.
       read_result cx r es = (INL v,es) /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory)
   | LocatedValue ann p => (p.ptr_location = LocMemory ==> !v tv w.
       read_result cx r es = (INL v,es) /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand p.ptr_operand s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory))
Proof
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (lb,sz)`],
      `aid < sa.cs_next_id` by decide_tac >>
      irule intcall_contained_bytes_frame >>
      qexistsl [`lb`, `sz`] >> simp[] >> metis_tac[])
  >>~- ([`local_region ce es.scopes s name lb sz`],
      irule intcall_contained_bytes_frame >>
      qexistsl [`lb`, `sz`] >> simp[] >> metis_tac[])
  >> simp[valueEncodingTheory.mem_bytes_at_def]
QED
