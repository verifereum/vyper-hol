Theory bodyAbiDecodeBytesPayloadGuardFiniteMods
Ancestors
  bodyFullAbiDecodeScalarObserved bodyFullAbiDecodeScalarNoAlloca
  abiBoundedBytesExecution abiDecodePtrBytesMember abiDecoderBytesBound
  abiDecoderReentry abiEncoder bodyPtrBopScalarOutcome
  appendStorageStageTransportPtr varsExt freshWrites emitHelper emitHelperProps
  exprLoweringProps compileEnv bodyPtrDefs loweringStateRelDefs
  bodyFullAbiDecodeInputOrigin fragGasOriginPtr fragGasPath fragExec
  venomExecSemantics venomState venomInst ptrDiscipline
  finite_map list rich_list pred_set words relation

(* The owned-state packet shared by the guarded decoder phases. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\ ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

fun close_packet tm =
  let val body = rhs (concl (DEPTH_CONV BETA_CONV tm))
  in list_mk_forall (free_vars_lr body, body) end;

val scalar_contract = close_packet ``
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    u = t with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    u.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo u /\
    (!op. op IN B ==> op_prov Gf op = NONE /\ op_taint tnf op = {}) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    (!D. RELPOW (\(v,Gv,tv) (z,Gz,tz).
       gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (v,Gv,tv) [] (OK z,Gz,tz))
       (LENGTH sb.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn) (u,Gf,tnf))``;

val payload_contract = close_packet ``
  abi_decode_bytes_payload_guard head cnt hi sc = ((),sg) /\ hi <> Lit 0w /\
  fn_has_code sc sg fn /\
  ~w.vs_halted /\ w.vs_current_bb = sc.cs_current_bb /\
  w.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (^owned_decoder_state) sc w Gw Tw /\ allocas_from lo w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  not_fresh_at sc input /\ local_ptrs_reserved ce sc /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  abi_decoder_operand_live sc.cs_next_var head /\
  abi_decoder_operand_live sc.cs_next_var cnt /\
  abi_decoder_operand_live sc.cs_next_var hi /\
  eval_operand head w = SOME (n2w (off+32)) /\
  eval_operand cnt w = SOME (n2w c) /\
  eval_operand hi w = SOME (n2w h) /\
  off+32 < dimword (:256) /\ c < dimword (:256) /\ h < dimword (:256) /\
  op_prov Gw head = NONE /\ op_taint Tw head = {} /\
  op_prov Gw cnt = NONE /\ op_taint Tw cnt = {} /\
  op_prov Gw hi = NONE /\ op_taint Tw hi = {} ==>
  (?y Gy Ty.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (w,Gw,Tw) [] (OK y,Gy,Ty)) /\
     ~y.vs_halted /\ y.vs_current_bb = sg.cs_current_bb /\
     y.vs_inst_idx = LENGTH sg.cs_current_insts /\
     (^owned_decoder_state) sg y Gy Ty /\ off+32+c <= h /\
     y.vs_memory = w.vs_memory /\ Ty.t_mem = Tw.t_mem /\ allocas_from lo y /\
     (!x. not_fresh_at sc x ==>
       lookup_var x y = lookup_var x w /\ FLOOKUP Gy x = FLOOKUP Gw x /\
       op_taint Ty (Var x) = op_taint Tw (Var x)) /\
     (!obs. fn_has_code sc sg obs ==> gas_path ctx obs w 0 (OK y)) /\
     cs_extends sc sg /\ LENGTH sc.cs_current_insts <= LENGTH sg.cs_current_insts /\
     sc.cs_next_var <= sg.cs_next_var /\ sc.cs_next_id <= sg.cs_next_id /\
     (!D. RELPOW (\(v,Gv,tv) (z,Gz,tz).
       gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (v,Gv,tv) [] (OK z,Gz,tz))
       (LENGTH sg.cs_current_insts - LENGTH sc.cs_current_insts) (w,Gw,Tw) (y,Gy,Ty))) \/
  (?z Gz Tz.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (w,Gw,Tw) [] (Abort Revert_abort z,Gz,Tz)) /\
     (!obs. fn_has_code sc sg obs ==> gas_path ctx obs w 0 (Abort Revert_abort z)))``;

Theorem bytes_payload_guard_finite:
  ^scalar_contract ==> ^payload_contract
Proof
  disch_then (mk_asm "scalar") >> rpt gen_tac >>
  qabbrev_tac `OS = (^owned_decoder_state)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
  `cs_extends sc sg /\ LENGTH sc.cs_current_insts <= LENGTH sg.cs_current_insts` by
    (conj_tac
     >- (irule cs_extends_same_block >> fs[inst_extends_def,IS_PREFIX_APPEND]) >>
     simp[inst_extends_def] >> fs[inst_extends_def]) >>
  `sc.cs_next_var <= sg.cs_next_var /\ sc.cs_next_id <= sg.cs_next_id` by
    (qpat_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `?B. bop_scalar_seq {x | not_fresh_at sc x} {head;cnt;hi} (emitted_insts sc sg) B /\
       {head;cnt;hi} SUBSET B` by
    (irule abi_decode_bytes_payload_scalar >> conj_tac >- simp[] >>
     qexistsl_tac [`head`,`hi`,`cnt`] >> simp[]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov Gw op = NONE /\ op_taint Tw op = {}` by
    (simp[] >> rpt strip_tac >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
          ~is_ext_call_op i.inst_opcode) (emitted_insts sc sg)` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o CONJUNCT1)
       bop_scalar_seq_outputs >> simp[is_terminator_def,is_ext_call_op_def]) >>
  `!op. abi_decoder_operand_live sc.cs_next_var op ==>
        eval_operand op (drop_fresh sc w) = eval_operand op w` by
    (gen_tac >> disch_tac >> irule eval_operand_drop_fresh >>
     qpat_x_assum `abi_decoder_operand_live sc.cs_next_var op` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `op` >>
     simp[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `eval_operand head (drop_fresh sc w) = SOME (n2w (off+32)) /\
   eval_operand cnt (drop_fresh sc w) = SOME (n2w c) /\
   eval_operand hi (drop_fresh sc w) = SOME (n2w h)` by simp[] >>
  `lo <= w.vs_alloca_next` by fs[Abbr `OS`] >>
  reverse (qsuff_tac `(?r. run_inst_seq (emitted_insts sc sg) w = Abort Revert_abort r) \/
    (?r. run_inst_seq (emitted_insts sc sg) w = OK r /\ off+32+c <= h)`)
  >- (assume_tac (Q.SPECL [`sc`,`w`] fresh_vars_wrt_drop_fresh) >>
      assume_tac (Q.SPECL [`sc`,`w`] vars_ext_drop_fresh) >>
      drule_all abi_decode_bytes_payload_guard_total >> strip_tac
      >- (disj1_tac >> drule_all run_inst_seq_vars_ext_abort >>
          disch_then (qx_choose_then `aw` strip_assume_tac) >>
          qexists_tac `aw` >> asm_rewrite_tac[]) >>
      disj2_tac >> drule_all_then (qx_choose_then `rw` strip_assume_tac)
        run_inst_seq_vars_ext_ok >>
      qexists_tac `rw` >> simp[] >>
      qpat_x_assum `w2n (n2w (off+32):bytes32) + w2n (n2w c:bytes32) <= _` mp_tac >>
      simp[w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `rr` assume_tac)
                              (qx_choose_then `rw` strip_assume_tac))
  >- (disj2_tac >> drule_all member_scalar_revert_observed >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  disj1_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sc sg)` by
    (drule abi_decode_scalar_seq_no_alloca >> simp[]) >>
  qpat_x_assum `Abbrev (OS = _)` (fn th =>
    asm_x "scalar" (mk_asm "scalar_OS" o
      PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  (* Instantiate the scalar packet by its reached code, then its raw run,
     before discharging the remaining owned-state conditions. *)
  asm_x "scalar_OS" drule >>
  ntac 5 (disch_then drule) >>
  ntac 3 (disch_then drule) >>
  ntac 3 (disch_then drule) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `y` (qx_choose_then `Gy` (qx_choose_then `Ty` strip_assume_tac)))) >>
  qexistsl_tac [`y`,`Gy`,`Ty`] >> asm_rewrite_tac[]
QED
