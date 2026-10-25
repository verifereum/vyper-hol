(* TOP-LEVEL: compile_create_allocation_execution, create_allocation_bounds,
   create_allocation_disjoint. Static buffers retain their instruction's
   allocation on re-entry. Natural allocator bounds must also exclude word wrap. *)
Theory createAllocationExecution
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps venomExecSemantics
  venomState venomInst venomMemDefs finite_map list words

Definition create_allocation_base_def:
  create_allocation_base (s:venom_state) (aid:num) =
    case FLOOKUP s.vs_allocas aid of
      NONE => s.vs_alloca_next
    | SOME (alloc_offset,alloc_capacity) => alloc_offset
End

Definition create_allocation_fields_def:
  create_allocation_fields (s:venom_state) (aid:num) (requested_size:num) =
    case FLOOKUP s.vs_allocas aid of
      SOME _ => s
    | NONE => s with
        <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,requested_size));
          vs_alloca_next := s.vs_alloca_next + requested_size|>
End

Theorem create_allocation_fields_frame[simp]:
  ∀s aid requested_size.
  (create_allocation_fields s aid requested_size).vs_vars = s.vs_vars ∧
  (create_allocation_fields s aid requested_size).vs_memory = s.vs_memory ∧
  (create_allocation_fields s aid requested_size).vs_accounts = s.vs_accounts ∧
  (create_allocation_fields s aid requested_size).vs_transient = s.vs_transient ∧
  (create_allocation_fields s aid requested_size).vs_call_ctx = s.vs_call_ctx
Proof
  rpt gen_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >>
  simp[create_allocation_fields_def]
QED

Theorem create_allocation_bounds:
  ∀s aid requested_size.
  alloca_next_valid s ∧
  (∀base stored. FLOOKUP s.vs_allocas aid = SOME (base,stored) ⇒ stored = requested_size) ∧
  s.vs_alloca_next + requested_size < 2 ** 256 ⇒
  create_allocation_base s aid + requested_size < 2 ** 256
Proof
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
  >- fs[create_allocation_base_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME allocation` >>
  PairCases_on `allocation` >> gvs[create_allocation_base_def] >>
  fs[alloca_next_valid_def] >> res_tac >> decide_tac
QED

Theorem create_allocation_disjoint:
  ∀s aid other base capacity requested_size.
  alloca_inv s ∧ aid ≠ other ∧
  FLOOKUP s.vs_allocas other = SOME (base,capacity) ∧
  (∀offset stored. FLOOKUP s.vs_allocas aid = SOME (offset,stored) ⇒ stored = requested_size) ⇒
  create_allocation_base s aid + requested_size ≤ base ∨
  base + capacity ≤ create_allocation_base s aid
Proof
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
  >- (fs[create_allocation_base_def, alloca_inv_def, alloca_next_valid_def] >>
      res_tac >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME allocation` >>
  PairCases_on `allocation` >>
  gvs[create_allocation_base_def, AllCaseEqs(), alloca_inv_def,
      allocas_non_overlapping_def] >>
  qpat_x_assum `∀a1 a2 b1 sz1 b2 sz2. _` drule_all >> simp[]
QED

Theorem compile_create_allocation_execution:
  ∀requested_size cs buf cs' s.
  compile_alloc_buffer requested_size cs = (buf,cs') ⇒
  ∃out. buf.buf_operand = Var out ∧ buf.buf_size = requested_size ∧
    run_inst_seq (emitted_insts cs cs') s =
      OK (update_var out (n2w (create_allocation_base s cs.cs_next_id))
            (create_allocation_fields s cs.cs_next_id (w2n (n2w requested_size : bytes32))))
Proof
  rpt gen_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_alloca_def,
       create_allocation_base_def, create_allocation_fields_def] >>
  Cases_on `FLOOKUP s.vs_allocas cs.cs_next_id` >>
  gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP s.vs_allocas cs.cs_next_id = SOME allocation` >>
  PairCases_on `allocation` >> simp[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createAllocationExecution");
