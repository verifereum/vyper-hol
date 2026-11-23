(* A scalar abort has one cursor and one ghost endpoint for every bound. *)
Theory augAssignFullScalarAbort
Ancestors
  augAssignPtrScalarRun fragGasCopyLoop fragGasCopySeqLiftProps fragGasSeqPtr
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  finite_map pred_set list rich_list

Theorem augassign_scalar_abort_uniform:
  scalar_code A code /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\
  run_inst_seq code s = Abort a t ==>
  ?j G' tn'.
    (!D. inst_seq_ptr D 0 ctx func PG G tn code s G' tn') /\
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort a (t with vs_inst_idx := j),G',tn')) /\
    (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
      FLOOKUP G' v = FLOOKUP G v /\
      FLOOKUP tn'.t_var v = FLOOKUP tn.t_var v /\
      op_taint tn' (Var v) = op_taint tn (Var v)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `?G' tn'. inst_seq_ptr ARB 0 ctx func PG G tn code s G' tn'` by
    (irule scalar_code_inst_seq_ptr_lo >>
     simp[allocas_from_def] >> qexists `A` >> simp[]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn code s G' tn'` by
    (gen_tac >>
     `?H tm. inst_seq_ptr D 0 ctx func PG G tn code s H tm` by
       (irule scalar_code_inst_seq_ptr_lo >>
        simp[allocas_from_def] >> qexists `A` >> simp[]) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) code` by gvs[EVERY_MEM] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     gvs[augAssignPtrScalarCertificateTheory.scalar_code_append,
         augAssignPtrScalarCertificateTheory.scalar_code_def,
         augAssignPtrScalarCertificateTheory.scalar_shape_def,
         augAssignPtrScalarCertificateTheory.scalar_binary_def,
         augAssignPtrScalarCertificateTheory.scalar_unary_def,
         unitTransformDefsTheory.dalloca_no_wrap_def]) >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qx_choose_then `j` assume_tac) >>
  qexistsl [`j`,`G'`,`tn'`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      irule inst_seq_ptr_lower_bound_transport >>
      simp[] >> conj_tac >- gvs[EVERY_MEM] >>
      qexists `0` >> simp[]) >>
  drule_all scalar_seq_metadata_frame_lo >> simp[]
QED
