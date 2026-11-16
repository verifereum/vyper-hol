(* The read-only ADD-32 suffix of the raw_call output buffer preparation. *)
Theory bodyFullRawCallOutbufAdd
Ancestors
  immutableRegionLoadPtr bodyFullUnwrapRun bodyFullGhostFrame
  ptrSafetyTransport fragGasSeqPtr fragExecMem instMemFrontier
  exprSimCopy exprLoweringProps emitHelperProps allocationPtr
  storageCopyBodyPtr decoderGhostFramePtr stmtAppendStorageRunPtr
  loweringStateRelDefs
  ptrDiscipline ptrSafeRun fragExecPtr
  venomExecSemantics venomState venomInst finite_map words list pred_set

Theorem raw_call_outbuf_add_joint:
  emit_op ADD [ov;Lit 32w] sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  fn_has_code sa sb func /\
  eval_operand ov s = SOME w /\ op_taint tn ov = {} /\
  op_prov G ov = SOME (b,n) /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G1 tn1.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G1,tn1)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |> = s /\
    eval_operand ov t = SOME w /\ eval_operand op t = SOME (w+32w) /\
    op_prov G1 ov = SOME (b,n) /\ op_prov G1 op = SOME (b,n) /\
    op_taint tn1 ov = {} /\ op_taint tn1 op = {} /\
    (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all emit_add_runtime_frame >> strip_tac >>
  `u = update_var out (w+32w) s` by gvs[copy_runtime_frame_def] >>
  gvs[] >>
  qexistsl [`step_prov PG G (mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out])
              (update_var out (w+32w) s)`,
            `tn with t_var := tn.t_var |+ (out,{})`] >>
  conj_tac
  >- (rpt gen_tac >>
      `inst_seq_ptr D 0 ctx func PG G tn
         [mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out]] s
         (step_prov PG G (mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out])
            (update_var out (w+32w) s))
         (tn with t_var := tn.t_var |+ (out,{}))` by
        (irule (SRULE [] (DISCH_ALL
           (Q.SPEC `s.vs_inst_idx` (UNDISCH_ALL clean_add_checked_uniform)))) >>
         simp[op_taint_def, eval_operand_def]) >>
      `inst_seq_ptr D lo ctx func PG G tn
         [mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out]] s
         (step_prov PG G (mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out])
            (update_var out (w+32w) s))
         (tn with t_var := tn.t_var |+ (out,{}))` by
        (gvs[inst_seq_ptr_def, storage_copy_add_step] >>
         irule ptr_inst_ok_lower_bound_transport >> simp[] >>
         qexists_tac `0` >> simp[]) >>
      `run_inst_seq_mem_ok [mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out]] s` by
        (simp[run_inst_seq_mem_ok_last] >>
         irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
      `sb.cs_current_insts = sa.cs_current_insts ++
         [mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out]] /\
       sb.cs_current_bb = sa.cs_current_bb` by
        gvs[copy_runtime_frame_def, same_blocks_def] >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                  ~is_terminator i.inst_opcode)
         [mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out]]` by
        simp[mk_inst_def, is_terminator_def] >>
      drule_all bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\ sa.cs_next_var <= sb.cs_next_var` by
    gvs[copy_runtime_frame_def, same_blocks_def] >>
  `!x. not_fresh_at sa x ==>
     FLOOKUP (step_prov PG G (mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out])
                (update_var out (w+32w) s)) x = FLOOKUP G x /\
     op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var x) =
       op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]) >>
  `op_prov (step_prov PG G (mk_inst sa.cs_next_id ADD [ov;Lit 32w] [out])
              (update_var out (w+32w) s)) (Var out) = SOME (b,n)` by
    simp[add_selected_provenance, first_prov_def] >>
  Cases_on `ov` >> gvs[op_prov_def] >>
  rename1 `not_fresh_at sa old` >>
  `old <> out` by metis_tac[] >>
  gvs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
      op_taint_def, venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  rpt strip_tac >> `x <> out` by metis_tac[] >> simp[]
QED
