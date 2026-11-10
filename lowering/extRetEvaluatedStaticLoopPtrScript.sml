Theory extRetEvaluatedStaticLoopPtr
Ancestors
  extRetEvaluatedStaticBodyPtr extRetLoopHeaderAmbientPtr extRetLoopTailAmbientPtr
  extRetAbiArrayStaticLoopPtr extRetAbiArrayHeaderPtr extRetRecursiveResourcePtr
  abiEncoderArrayHeader abiEncoderArrayBodyCode abiDecoderLoopEmit
  fragExec fragGasPathPtr compileEnv emitHelperProps ptrDiscipline bodyPtrDefs
  venomState venomExecSemantics words finite_map list rich_list arithmetic pred_set
  valueEncoding valueEncodingProofs vyperTypeABI vyperTyping

Theorem encoder_static_loop_header_ambient_counted_ptr:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  fn_has_code sh sb fn /\ not_fresh_at sh cv /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ptr_covers G tn ip s 32 /\ lookup_var ip s = SOME p /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  lookup_var cv s = SOME (n2w n) /\
  mload (w2n p) s = n2w j /\ j <= n /\ n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
    sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qabbrev_tac `iv = STRING #"%" (toString sh.cs_next_var)` >>
  qabbrev_tac `cmp = STRING #"%" (toString (sh.cs_next_var+1))` >>
  qabbrev_tac `done = STRING #"%" (toString (sh.cs_next_var+2))` >>
  `!v. not_fresh_at sh v ==> v <> iv /\ v <> cmp /\ v <> done` by
    (gvs[not_fresh_at_def, Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  drule_all abi_encode_array_header_code_ptr >> strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w n) /\ cv <> iv` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `bb.bb_instructions = abi_encode_array_header_insts (sh.cs_next_id+1)
    (Var ip) (Var cv) iv cmp done body_lbl exit_lbl` by
    simp[Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all (abi_encode_array_header_ambient_counted_ptr |>
    Q.INST [`count_op` |-> `Var cv`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,
    `jump_to (if j<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j n s)`] >>
  simp[jump_to_def, abi_encode_array_header_state_def, update_var_def] >>
  rpt strip_tac >>
  `v <> iv /\ v <> cmp /\ v <> done` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Definition encoder_static_loop_inv_def:
  encoder_static_loop_inv ctx fn sites q len protected
      ip src dst cv p a b scap dcap tv maxn vs k j G tn s <=>
    ~s.vs_halted /\
    lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\
    lookup_var dst s = SOME b /\ lookup_var cv s = SOME (n2w (LENGTH vs)) /\
    ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
    mload (w2n p) s = n2w j /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
    op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
    (!i. w2n b <= i /\ i < w2n b+32+j*k ==> i NOTIN tn.t_mem) /\
    encoder_resource ctx fn sites q len protected s
End

Theorem encoder_static_loop_inv_memory_frame[local]:
  encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j G tn s /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  ~sf.vs_halted /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
  sf.vs_fmp = s.vs_fmp /\
  (!v. not_fresh_at sh v ==>
    lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)) ==>
  encoder_static_loop_inv ctx fn sites q len protected
    ip src dst cv p a b scap dcap tv maxn vs k j Gf tnf sf
Proof
  strip_tac >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_fields >> metis_tac[encoder_static_loop_inv_def]) >>
  gvs[encoder_static_loop_inv_def, mload_def, ptr_covers_def, op_prov_def] >>
  metis_tac[]
QED
