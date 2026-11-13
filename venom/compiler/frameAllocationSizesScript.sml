Theory frameAllocationSizes
Ancestors
  frameOriginCache ptrDisciplineEmptyTaint venomMemProps
  venomExecSemantics venomState finite_map list words

Definition cache_sizes_ok_def:
  cache_sizes_ok M s <=>
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      FLOOKUP M aid = SOME sz
End

Theorem cache_sizes_ok_empty:
  s.vs_allocas = FEMPTY ==> cache_sizes_ok M s
Proof
  simp[cache_sizes_ok_def]
QED

Theorem cache_sizes_ok_transport:
  cache_sizes_ok M s /\ s'.vs_allocas = s.vs_allocas ==>
  cache_sizes_ok M s'
Proof
  simp[cache_sizes_ok_def]
QED

Theorem cache_sizes_ok_lookup:
  cache_sizes_ok M s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  FLOOKUP M aid = SOME sz
Proof
  metis_tac[cache_sizes_ok_def]
QED

Theorem cache_sizes_ok_alloca:
  cache_sizes_ok M s /\ FLOOKUP M inst.inst_id = SOME (w2n n) /\
  exec_alloca inst s n = OK s' ==> cache_sizes_ok M s'
Proof
  rw[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  gvs[cache_sizes_ok_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `aid = inst.inst_id` >> gvs[] >> metis_tac[]
QED

Theorem cache_sizes_ok_step:
  cache_sizes_ok M s /\ step_inst fuel ctx inst s = OK s' /\
  inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode = ALLOCA ==> ?n rest.
    inst.inst_operands = Lit n :: rest /\
    FLOOKUP M inst.inst_id = SOME (w2n n)) ==>
  cache_sizes_ok M s'
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >>
      metis_tac[cache_sizes_ok_alloca]) >>
  irule cache_sizes_ok_transport >> qexists_tac `s` >> simp[] >>
  metis_tac[step_inst_base_preserves_allocas]
QED

Theorem cache_sizes_ok_entry:
  cache_sizes_ok M s /\ enters_block fn s s1 ==> cache_sizes_ok M s1
Proof
  metis_tac[cache_sizes_ok_transport, enters_block_allocas]
QED

Theorem cache_sizes_ok_return:
  cache_sizes_ok M caller /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME s' ==>
  cache_sizes_ok M (s' with vs_inst_idx := idx)
Proof
  metis_tac[cache_sizes_ok_transport, return_bind_cache]
QED

(* Interface probes: neither cache contents nor the allocator cursor must
   initially be zero.  A cache hit need not use the current size operand. *)
Theorem cache_sizes_empty_probe[local]:
  cache_sizes_ok M (s with <|vs_allocas := FEMPTY; vs_alloca_next := next|>)
Proof
  simp[cache_sizes_ok_def]
QED

Theorem cache_sizes_hit_probe[local]:
  inst.inst_id = aid /\ inst.inst_outputs = [out] ==>
  cache_sizes_ok (FEMPTY |+ (aid,sz))
    (update_var out (n2w baddr)
      (s with <|vs_allocas := FEMPTY |+ (aid,(baddr,sz));
                vs_alloca_next := next|>)) /\
  exec_alloca inst
    (s with <|vs_allocas := FEMPTY |+ (aid,(baddr,sz));
              vs_alloca_next := next|>) n =
  OK (update_var out (n2w baddr)
    (s with <|vs_allocas := FEMPTY |+ (aid,(baddr,sz));
              vs_alloca_next := next|>))
Proof
  simp[cache_sizes_ok_def, exec_alloca_def, update_var_def,
       FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[]
QED

Theorem cache_sizes_zero_probe[local]:
  inst.inst_outputs = [out] ==>
  exec_alloca inst
    (s with <|vs_allocas := FEMPTY; vs_alloca_next := next|>) 0w =
  OK (update_var out (n2w next)
    (s with <|vs_allocas := FEMPTY |+ (inst.inst_id,(next,0));
              vs_alloca_next := next|>)) /\
  cache_sizes_ok (FEMPTY |+ (inst.inst_id,0))
    (s with <|vs_allocas := FEMPTY |+ (inst.inst_id,(next,0));
              vs_alloca_next := next|>)
Proof
  simp[exec_alloca_def, cache_sizes_ok_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED
