Theory bodyPtrIntCallPrologue
Ancestors
  bodyPtrIntCallEntryMaterialize bodyPtrIntCallMaterializeList allocationPtr robustCopyTransportPtr
  fragGasSeqPtr intCallCallee venomState venomExecSemantics ptrDiscipline
  finite_map words exprLoweringProps bodyPtrDefs pred_set loweringHalt
  fragExecPtr venomInst arithmetic emitHelper exprLowering compileEnv

(* Scratch allocation taints only bytes above the completed locals. *)
Theorem intcall_scratch_old_robust:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  val_wf ty v /\ p + val_footprint ty v <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ty v p m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
    u.vs_memory m ==> val_in_memory ty v p m
Proof
  rpt gen_tac >> strip_tac >>
  `u.vs_memory = s.vs_memory` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
     gvs[update_var_def]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`,`FEMPTY`,`tn`] strip_assume_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  simp[] >>
  qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem`,
    `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}`] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem intcall_scratch_local_value:
  intcall_local_value entry p sz G tn s /\ p <> out /\
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  intcall_local_value entry p sz
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >>
  `n < dimword (:256)` by decide_tac >>
  fs[intcall_local_value_def] >>
  `lookup_var p u = lookup_var p s /\ s.vs_alloca_next <= u.vs_alloca_next` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) p u sz` by
    (irule (cj 2 fresh_alloca_ptr_covers) >> asm_rewrite_tac[] >> simp[]) >>
  asm_rewrite_tac[] >> qexists_tac `w` >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  metis_tac[intcall_scratch_old_robust]
QED

Theorem intcall_scratch_completed:
  intcall_completed env ce G tn s /\
  (!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  intcall_completed env ce
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  simp[intcall_completed_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`p`,`sz`] >> asm_rewrite_tac[] >>
  irule intcall_scratch_local_value >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >> decide_tac
QED

Theorem intcall_scratch_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w n)] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ALLOCA [Lit (n2w n)] [out]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)` by
    (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_alloca >> simp[]) >>
  `run_inst_seq [mk_inst id ALLOCA [Lit (n2w n)] [out]] s = OK u` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id ALLOCA [Lit (n2w n)] [out]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def, is_terminator_def, ADD1]
QED

Theorem intcall_prologue_factor:
  compile_internal_prologue ce params has_rb ret_type st0 = ((ce2,rpc),st1) ==>
  ?ce1 caps stm st2.
    compile_internal_entry_prefix ce params has_rb st0 = ((ce1,caps,rpc),stm) /\
    materialize_internal_params ce1 caps stm = (ce2,st2) /\
    (case ret_type of
       SOME ty => if ce.ce_returns_count > 0 then
         do compile_alloc_buffer (type_memory_bytes ce ty); return () od
         else return ()
     | NONE => return ()) st2 = ((),st1)
Proof
  simp[compile_internal_prologue_def, compile_internal_entry_prefix_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
