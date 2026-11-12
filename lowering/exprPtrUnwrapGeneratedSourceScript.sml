(* Concrete generated source prefix. Ghost endpoints remain explicit so
   consumers infer them from equations, rather than unpacking existentials. *)
Theory exprPtrUnwrapGeneratedSource
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapFrames exprPtrUnwrapCopyEdges typedCopyPtr
  slotCopyExecution copyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map exprLoweringProps decoderGhostFramePtr ghostPcTransportPtr

Theorem copy_generated_source_checks:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME a /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var (slot_copy_var cs 2) (a+k) s /\
  w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s u tn /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3])
    (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w) /\
  tnf = step_taint (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) w
    (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w) tm ==>
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]] s Gf tnf
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem copy_generated_source_ghost:
  (load = SLOAD \/ load = TLOAD) /\
  u = update_var (slot_copy_var cs 2) (a+k) s /\
  w = u /\ 
  H = step_prov PG G (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+4) ADD
    [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s u tn /\
  v = update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k)) w /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) v /\
  tnf = step_taint (mk_inst (cs.cs_next_id+5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) w v tm ==>
  op_taint tnf (Var (slot_copy_var cs 3)) =
    key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (a+k) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 ==>
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem copy_generated_source_execution:
  (load=SLOAD \/ load=TLOAD) /\ eval_operand src s = SOME a /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k ==>
  run_inst_seq
    [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]] s =
  OK (update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k))
       (update_var (slot_copy_var cs 2) (a+k) s))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED


Theorem copy_generated_source_segment:
  (load=SLOAD \/ load=TLOAD) /\ eval_operand src s = SOME a /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 3) (slot_copy_word load s (a+k))
       (update_var (slot_copy_var cs 2) (a+k) s) /\
    run_inst_seq
      [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
       mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]] s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
       mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]]
      (s with vs_inst_idx := ix) Gf tnf) /\
    op_taint tnf (Var (slot_copy_var cs 3)) =
      key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (a+k) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED
