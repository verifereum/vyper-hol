(* ci_mono omits allocation-output origins and the new current-list shape
   after block switches. This proof interface retains both in one trace. *)
Theory bodyPtrBytestringBuiltinsAllocationTrace
Ancestors bodyPtrBytestringBuiltinsImageProtectedIdentity
          bodyPtrBytestringBuiltinsImageTupleHistory
          bodyPtrBytestringBuiltinsAllocationOrigins loweringShapeDefs
          compileEnv emitHelper venomInst list arithmetic ASCIInumbers

Definition allocation_trace_def:
  allocation_trace sa sb <=>
    sa.cs_next_var <= sb.cs_next_var /\
    ?delta. state_insts sb = state_insts sa ++ delta /\
      alloca_output_interval sa.cs_next_var sb.cs_next_var delta /\
      (sb.cs_current_insts = sa.cs_current_insts ++ delta \/
       ?prefix. delta = prefix ++ sb.cs_current_insts)
End

Theorem allocation_trace_refl[simp]:
  allocation_trace st st
Proof
  simp[allocation_trace_def] >> qexists_tac `[]` >> simp[]
QED

Theorem allocation_trace_trans:
  allocation_trace sa sb /\ allocation_trace sb sc ==> allocation_trace sa sc
Proof
  rewrite_tac[allocation_trace_def] >> strip_tac >> (
  conj_tac >- decide_tac >>
  rename1 `state_insts sb = state_insts sa ++ d1` >>
  rename1 `state_insts sc = state_insts sb ++ d2` >>
  qexists_tac `d1 ++ d2` >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac >- metis_tac[alloca_output_interval_append] >>
  metis_tac[APPEND_ASSOC])
QED

Theorem allocation_trace_return[simp]:
  allocation_trace st (SND (comp_return v st))
Proof
  simp[comp_return_def]
QED

Theorem allocation_trace_bind:
  (!s. allocation_trace s (SND (f s))) /\
  (!v s. allocation_trace s (SND (g v s))) ==>
  !s. allocation_trace s (SND (comp_bind f g s))
Proof
  simp[comp_bind_def] >> rpt strip_tac >> pairarg_tac >> gvs[] >>
  metis_tac[allocation_trace_trans, pairTheory.SND]
QED

Theorem allocation_trace_ignore_bind:
  (!s. allocation_trace s (SND (f s))) /\
  (!s. allocation_trace s (SND (g s))) ==>
  !s. allocation_trace s (SND (comp_ignore_bind f g s))
Proof
  simp[comp_ignore_bind_def, allocation_trace_bind]
QED

Theorem allocation_trace_emit:
  emit inst sa = (u,sb) /\
  (inst.inst_opcode = ALLOCA ==> !x. MEM x inst.inst_outputs ==>
    ?k. x = STRING #"%" (toString k) /\
        sa.cs_next_var <= k /\ k < sa.cs_next_var) ==>
  allocation_trace sa sb
Proof
  strip_tac >> drule_all raw_emit_alloca_origin >> strip_tac >>
  simp[allocation_trace_def] >> gvs[emit_def] >>
  qexists_tac `[inst]` >> simp[]
QED

Theorem allocation_trace_new_block:
  new_block lbl sa = (u,sb) ==> allocation_trace sa sb
Proof
  strip_tac >> drule state_insts_new_block >> strip_tac >>
  simp[allocation_trace_def] >> gvs[new_block_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem allocation_trace_emit_op:
  emit_op opc args sa = (op,sb) ==> allocation_trace sa sb
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[allocation_trace_def, state_insts_def, all_blocks_def,
      FLAT_APPEND, APPEND_ASSOC] >>
  simp[alloca_output_interval_def, mk_inst_def]
QED

Theorem allocation_trace_fresh_var:
  fresh_var sa = (x,sb) ==> allocation_trace sa sb
Proof
  strip_tac >> drule state_insts_fresh_var >> strip_tac >>
  simp[allocation_trace_def] >> gvs[fresh_var_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem allocation_trace_fresh_id:
  fresh_id sa = (x,sb) ==> allocation_trace sa sb
Proof
  strip_tac >> drule state_insts_fresh_id >> strip_tac >>
  simp[allocation_trace_def] >> gvs[fresh_id_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem allocation_trace_fresh_label:
  fresh_label suffix sa = (x,sb) ==> allocation_trace sa sb
Proof
  strip_tac >> drule state_insts_fresh_label >> strip_tac >>
  simp[allocation_trace_def] >> gvs[fresh_label_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem allocation_interval_excludes_old:
  alloca_output_interval lo hi code /\ k < lo ==>
  EVERY (\inst. !i w v. Var (STRING #"%" (toString k)) = Var v ==>
    inst <> mk_inst i ALLOCA [Lit w] [v]) code
Proof
  simp[alloca_output_interval_def, EVERY_MEM, mk_inst_def] >>
  rpt strip_tac >>
  gvs[] >> first_x_assum drule >> simp[] >>
  disch_then (qspec_then `STRING #"%" (toString k)` mp_tac) >>
  simp[] >> decide_tac
QED

Theorem allocation_trace_protected_tail:
  allocation_trace sa sb /\ k < sa.cs_next_var ==>
  (tail_alloc (Var (STRING #"%" (toString k))) sb.cs_current_insts ==>
   tail_alloc (Var (STRING #"%" (toString k))) sa.cs_current_insts)
Proof
  simp[allocation_trace_def] >> strip_tac
  >- (drule_all allocation_interval_excludes_old >> strip_tac >>
      metis_tac[tail_alloc_frame]) >>
  `alloca_output_interval sa.cs_next_var sb.cs_next_var sb.cs_current_insts` by
    (gvs[alloca_output_interval_def, MEM_APPEND] >> metis_tac[]) >>
  drule_all allocation_interval_excludes_old >> strip_tac >>
  metis_tac[tail_alloc_excluded]
QED

Theorem allocation_trace_emit_void:
  emit_void opc args sa = (u,sb) ==> allocation_trace sa sb
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >>
  gvs[allocation_trace_def, state_insts_def, all_blocks_def,
      FLAT_APPEND, APPEND_ASSOC] >>
  simp[alloca_output_interval_def, mk_inst_def]
QED

Theorem allocation_trace_emit_inst:
  (opc = ALLOCA ==> outs = []) /\
  emit_inst opc args outs sa = (u,sb) ==> allocation_trace sa sb
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >>
  gvs[allocation_trace_def, state_insts_def, all_blocks_def,
      FLAT_APPEND, APPEND_ASSOC] >>
  simp[alloca_output_interval_def, mk_inst_def]
QED
