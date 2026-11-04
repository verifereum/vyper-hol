(* Local GAS residuals do not require a callee to return. *)
Theory dftOccurrenceOpenCall
Ancestors
  dftOccurrenceReturn dftOccurrenceReceipt dftOccurrenceResidual
  dftOccurrenceMachine dftOccurrenceReplay list sorting

Theorem dft_gas_cut_operands:
  dft_cut_pair [(v,g)] [] s t /\ ~MEM (Var v) ops ==>
  eval_operands ops s = eval_operands ops t
Proof
  strip_tac >> irule dft_cut_pair_eval_operands >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem dft_gas_cut_setup:
  dft_cut_pair [(v,g)] [] s t ==>
  setup_callee fn args s = setup_callee fn args t
Proof
  metis_tac[dft_cut_pair_setup_callee]
QED

Theorem dft_gas_saved_call:
  dft_receipt w lctx lc0 H h gas addr [(v,w addr)] /\
  dft_cut_pair [(v,w addr)] [] s t /\ ~MEM v outs ==>
  dft_saved_call w lctx lc0 H [(h,gas,addr,[(v,w addr)])]
    rctx rc0 rh [] outs s t
Proof
  simp[dft_saved_call_def, dft_receipt_list_def,
       dft_receipt_payload_def, SORTED_DEF]
QED

Theorem dft_gas_cut_return:
  dft_cut_pair [(v,g)] [] s t /\ ~MEM v outs /\
  dft_restore outs ret cs s = SOME s' /\
  dft_restore outs ret cs t = SOME t' ==>
  dft_cut_pair [(v,g)] [] s' t'
Proof
  strip_tac >> irule dft_restore_cut_pair >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem dft_open_call_address:
  c.dft_occ_path = d.dft_occ_path /\
  c.dft_occ_visit = d.dft_occ_visit ==>
  c.dft_occ_path ++ [(c.dft_occ_visit,inst.inst_id)] =
  d.dft_occ_path ++ [(d.dft_occ_visit,inst.inst_id)]
Proof
  simp[]
QED

(* Instantiate once for each side; the counters and saved stacks are independent. *)
Theorem dft_gas_cut_push:
  dft_cut_pair [(v,g)] [] sL sR /\ ~MEM (Var v) ops /\
  eval_operands ops sL = SOME args /\ setup_callee callee args sL = SOME cs /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb sR) stack n /\
  get_instruction bb sR.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee ==>
  dft_occ_oracle_next w ctx c = c with
    <|dft_occ_core := dft_erase (DftOpen (DftEnter callee 1 cs)
        (DftCaller fn 1 bb inst sR :: MAP (dft_fill_frame 1) stack) n);
      dft_occ_path := c.dft_occ_path ++ [(c.dft_occ_visit,inst.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved|>
Proof
  strip_tac >>
  `eval_operands ops sL = eval_operands ops sR` by
    (irule dft_gas_cut_operands >> simp[] >> metis_tac[]) >>
  `setup_callee callee args sL = setup_callee callee args sR` by
    (irule dft_gas_cut_setup >> metis_tac[]) >>
  rewrite_tac[dft_occ_oracle_next_def] >> irule dft_occ_push >> simp[] >>
  qexists_tac `args` >> metis_tac[]
QED

Theorem dft_gas_orbit_saved_call:
  h < H /\ c = FUNPOW (dft_occ_oracle_next w lctx) h lc0 /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  dft_occ_event gas addr c /\ gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  dft_cut_pair [(v,w addr)] [] sL sR /\ ~MEM v outs ==>
  dft_saved_call w lctx lc0 H [(h,gas,addr,[(v,w addr)])]
    rctx rc0 rh [] outs sL sR
Proof
  strip_tac >> irule dft_gas_saved_call >> simp[] >>
  irule dft_receipt_gas >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
