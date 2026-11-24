(* Uniform ghost endpoint for a successful scalar instruction run. *)
Theory augAssignFullScalarSuccess
Ancestors
  augAssignPtrScalarRun augAssignPtrScalarCertificate fragGasSeqPtr fragGasCopyLoop
  fragGasCopySeqLiftProps
  ptrDiscipline ptrSafeRun fragExec fragExecMem venomExecSemantics
  venomState venomInst finite_map pred_set list rich_list

Theorem augassign_scalar_success_uniform:
  scalar_code A code /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code))) result /\
  run_inst_seq code s = OK t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq_mem_ok code s /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code ==>
  ?G' tn'.
    (!D. inst_seq_ptr D 0 ctx func PG G tn code s G' tn') /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn') /\
      allocas_from lo t) /\
    op_prov G' result = NONE /\ op_taint tn' result = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
      FLOOKUP G' v = FLOOKUP G v /\
      FLOOKUP tn'.t_var v = FLOOKUP tn.t_var v /\
      op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     fs[scalar_code_append, scalar_code_def] >>
     qpat_x_assum `scalar_shape i` mp_tac >>
     simp[scalar_shape_def, scalar_binary_def, scalar_unary_def] >>
     rpt strip_tac >> gvs[]) >>
  `?H tm. inst_seq_ptr ARB 0 ctx func PG G tn code s H tm` by
    (irule scalar_code_inst_seq_ptr_lo >>
     simp[allocas_from_def] >> qexists `A` >> simp[]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn code s H tm` by
    (gen_tac >>
     `?J tj. inst_seq_ptr D 0 ctx func PG G tn code s J tj` by
       (irule scalar_code_inst_seq_ptr_lo >>
        simp[allocas_from_def] >> qexists `A` >> simp[]) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  qexistsl [`H`, `tm`] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >>
     `inst_seq_ptr D 0 ctx func PG G tn code s H tm` by simp[] >>
     drule_all run_inst_seq_origin_ptr_lift >> simp[]) >>
  `!v. v IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) ==>
       op_prov H (Var v) = NONE /\ op_taint tm (Var v) = {}` by
    (metis_tac[scalar_seq_success_clean]) >>
  drule_all scalar_available_clean >> strip_tac >>
  drule_all scalar_seq_metadata_frame_lo >> simp[]
QED
