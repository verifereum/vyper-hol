(* Generated MUL/ADD address prefix, with concrete ghost endpoints. *)
Theory exprPtrUnwrapGeneratedDestination
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapCopyEdges exprPtrUnwrapFrames
  typedCopyPtr typedCopyLoopHeaderPtr decoderGhostFramePtr
  slotCopyExecution copyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  exprLoweringProps ghostPcTransportPtr

Theorem copy_generated_destination_covers:
  lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ root <> slot_copy_var cs 4 /\
  root <> slot_copy_var cs 5 /\ 
  off < capacity /\ off + 32 <= capacity /\ w2n a + off < dimword(:256) /\
  u = update_var (slot_copy_var cs 4) (n2w off) s /\
  w = (u with vs_inst_idx := ix) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn /\
  v = update_var (slot_copy_var cs 5) (a+n2w off) w /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) v /\
  tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w v tm ==>
  ptr_covers Gf tnf (slot_copy_var cs 5) v 32
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem copy_generated_destination_checks:
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ k*32w = n2w off /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  root <> slot_copy_var cs 4 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var (slot_copy_var cs 4) (n2w off) s /\
  w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5])
    (update_var (slot_copy_var cs 5) (a+n2w off) w) /\
  tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w
    (update_var (slot_copy_var cs 5) (a+n2w off) w) tm ==>
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]] s Gf tnf
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem copy_generated_destination_ghost:
  u = update_var (slot_copy_var cs 4) (n2w off) s /\
  w = (u with vs_inst_idx := ix) /\
  H = step_prov PG G (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) u /\
  tm = step_taint (mk_inst (cs.cs_next_id+6) MUL
    [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4]) s u tn /\
  v = update_var (slot_copy_var cs 5) (a+n2w off) w /\
  Gf = step_prov PG H (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) v /\
  tnf = step_taint (mk_inst (cs.cs_next_id+7) ADD
    [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) w v tm ==>
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 ==>
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem copy_generated_destination_execution:
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\ k*32w = n2w off /\
  lookup_var root s = SOME a /\ root <> slot_copy_var cs 4 ==>
  run_inst_seq
    [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]] s =
  OK (update_var (slot_copy_var cs 5) (a+n2w off)
        (update_var (slot_copy_var cs 4) (n2w off) s))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem copy_generated_destination_segment:
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ k*32w = n2w off /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5 /\
  off < capacity /\ off+32 <= capacity /\ w2n a+off < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 5) (a+n2w off)
          (update_var (slot_copy_var cs 4) (n2w off) s) /\
    run_inst_seq
      [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
       mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]] s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
       mk_inst (cs.cs_next_id+7) ADD [Var root;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]]
      (s with vs_inst_idx := ix) Gf tnf) /\
    ptr_covers Gf tnf (slot_copy_var cs 5) t 32 /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED
