(* The data pointer following a slice buffer's allocation. *)
Theory bodyFullBuiltinBytestringBuffer
Ancestors
  bodyFullAllocaFresh bodyFullUnwrapRun bodyPtrBytestringBuiltinsBuffer
  bodyPtrBytestringBuiltinsAllocation typedCopyPtr fragExec fragExecMem fragExecPtr
  fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport instMemFrontier
  memSafeRun ptrDiscipline bodyPtrDefs venomExecSemantics venomState venomInst
  emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  context words list finite_map

Theorem bytestring_data_offset_full_run:
  emit_op ADD [Var root;Lit 32w] sa = (Var data,sb) /\
  fn_has_code sa sb func /\ root <> data /\
  lookup_var root s = SOME b /\ ptr_covers G tn root s N /\
  32 <= N /\ w2n b + 32 < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    t = update_var data (b+32w) s with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var root t = SOME b /\ lookup_var data t = SOME (b+32w) /\
    ptr_covers G' tn' root t N /\ ptr_covers G' tn' data t (N-32) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var root;Lit 32w] [data]` >>
  qabbrev_tac `u = update_var data (b+32w) s` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [i] /\
   !x. not_fresh_at sa x ==> x <> data` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def, Abbr `i`] >>
     simp[not_fresh_at_def]) >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def] >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i] s
     (step_prov PG G i u) (step_taint i s u tn)` by
    (gen_tac >> simp[inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def]) >>
  `run_inst_seq [i] s = OK u /\ run_inst_seq_mem_ok [i] s /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) [i]` by
    simp[run_inst_seq_def, run_inst_seq_mem_ok_last, Abbr `i`,
         mk_inst_def, is_terminator_def, below_frontier_no_ranges,
         inst_dload_in_section_def] >>
  `ptr_covers (step_prov PG G i u) (step_taint i s u tn)
     data (u with vs_inst_idx := SUC s.vs_inst_idx) (N-32)` by
    (simp[Abbr `i`, Abbr `u`] >>
     mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`sa.cs_next_id`,`root`,`data`,
       `b`,`32`,`N`,`N-32`,`Lit 32w`] pointer_offset_covers) >>
     simp[eval_operand_def, op_taint_def]) >>
  `op_taint (step_taint i s u tn) (Var data) = {} /\
   (step_taint i s u tn).t_mem = tn.t_mem /\
   (step_taint i s u tn).t_stor = tn.t_stor /\
   (step_taint i s u tn).t_trans = tn.t_trans /\
   (!x. x <> data ==> FLOOKUP (step_prov PG G i u) x = FLOOKUP G x /\
     op_taint (step_taint i s u tn) (Var x) = op_taint tn (Var x))` by
    simp[Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame] >>
  `(step_taint i s u tn).t_imm = tn.t_imm` by
    simp[Abbr `i`, step_taint_def, imm_taint_def, mk_inst_def] >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,
                `step_prov PG G i u`,`step_taint i s u tn`] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac
  >- (gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`[i]`,`sa`] >> simp[]) >>
  simp[Abbr `u`, lookup_var_update_var, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  conj_tac
  >- (fs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  conj_tac
  >- (fs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  fs[update_var_def] >>
  metis_tac[]
QED
