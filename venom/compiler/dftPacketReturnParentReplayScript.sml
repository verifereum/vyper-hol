Theory dftPacketReturnParentReplay
Ancestors
  dftPacketReturnRowSupply dftPacketNativeRowReplay
  dftGasFromListRestore dftRunRel finite_map list rich_list arithmetic

(* A return changes no field on which historical caller agreement depends. *)
Theorem dft_packet_return_historical_Q_frame:
  FLOOKUP (calls : (gas_event,
    num # num # venom_state # num list # venom_state #
    (internal_return # venom_state # venom_state) option) fmap)
    (a0,e0,cid0) = SOME(q0,h0,b0,done0,entry0,NONE) /\
  (!a e cid q h b done entry ret
      bb bt ps xs ys rho in_state bh be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME(q,h,b,done,entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME(bb,bt,ps,xs,ys,rho,in_state,bh,SOME(be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b.vs_gas_readings) =
        setup_callee callee args b)) ==>
  (!a e cid q h b done entry ret
      bb bt ps xs ys rho in_state bh be hbe count front closed brest ms.
    FLOOKUP (calls |+ ((a0,e0,cid0),(q0,h0,b0,done0,entry0,SOME(ir,out,post))))
      (a,e,cid) = SOME(q,h,b,done,entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME(bb,bt,ps,xs,ys,rho,in_state,bh,SOME(be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b.vs_gas_readings) =
        setup_callee callee args b))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `(a0,e0,cid0) = (a,e,cid)` >> gvs[FLOOKUP_UPDATE] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

(* The calls supplied here are the final retained records.  A completed child
   is either already closed in acts, or is the child whose return is being
   installed.  Its certificate is explicit in the latter case. *)
Theorem dft_packet_return_parent_U:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH xs /\ LENGTH ks = LENGTH xs /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  (!q. q < LENGTH xs ==>
    ((EL q xs).inst_opcode = GAS ==>
      EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
      EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
      EL q ks = [(a,e,(EL q xs).inst_id)]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
    ((EL q xs).inst_opcode = INVOKE ==>
      EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
      EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
      EL q ks = AK ((e,(EL q xs).inst_id)::a))) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
    MEM q (TAKE (SUC cnt) sched) ==>
    ?h b0 done entry ir out post nm ops ctf args.
      FLOOKUP (calls : (gas_event,
        num # num # venom_state # num list # venom_state #
        (internal_return # venom_state # venom_state) option) fmap)
        (a,e,(EL q xs).inst_id) = SOME(q,h,b0,done,entry,SOME(ir,out,post)) /\
      decode_invoke (EL q xs) = SOME(nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME entry /\
      (!csf. lookup_function nm C7.ctx_functions = SOME csf ==>
        (?ord rest. FLOOKUP (acts : ((num # num) list,
          ir_function # ir_function # num # venom_state # num list #
          exec_result option # bytes32 list option) fmap)
          ((e,(EL q xs).inst_id)::a) =
            SOME(csf,ctf,e,entry,ord,SOME(IntRet ir out),SOME rest)) \/
        ((e,(EL q xs).inst_id)::a = child0 /\ csf = csf0 /\ entry = entry0 /\
          ir = ir0 /\ out = out0))) /\
  (!q h b0 done entry ir out post.
    FLOOKUP calls (a,e,(EL q xs).inst_id) = SOME(q,h,b0,done,entry,SOME(ir,out,post)) ==>
    !F pg rest u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) pg /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT pg ++ rest) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0)) /\
  (!child csf ctf inc entry ord ir out rest.
    FLOOKUP acts child = SOME(csf,ctf,inc,entry,ord,SOME(IntRet ir out),SOME rest) ==>
    !F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM child) gs ==>
      (?extra. AE child = gas_events_blocks (F-inc) C7 csf
        (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
      (terminates (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail)) ==>
        residual_result tail (IntRet ir out)
          (run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail)) /\
        gas_events_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = AE child) /\
      (!ret v. run_blocks (F-inc) C7 csf (entry with vs_gas_readings := gs ++ tail) = IntRet ret v ==>
        trace_gas (trace_blocks child inc (F-inc) C7 csf
          (entry with vs_gas_readings := gs ++ tail)) = ZIP(AK child,gs))) /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM child0) gs ==>
    (?extra. AE child0 = gas_events_blocks (F-e) C7 csf0
      (entry0 with vs_gas_readings := gs ++ tail) ++ extra) /\
    (terminates (run_blocks (F-e) C7 csf0 (entry0 with vs_gas_readings := gs ++ tail)) ==>
      residual_result tail (IntRet ir0 out0)
        (run_blocks (F-e) C7 csf0 (entry0 with vs_gas_readings := gs ++ tail)) /\
      gas_events_blocks (F-e) C7 csf0 (entry0 with vs_gas_readings := gs ++ tail) = AE child0) /\
    (!ret v. run_blocks (F-e) C7 csf0 (entry0 with vs_gas_readings := gs ++ tail) = IntRet ret v ==>
      trace_gas (trace_blocks child0 e (F-e) C7 csf0
        (entry0 with vs_gas_readings := gs ++ tail)) = ZIP(AK child0,gs))) ==>
  !F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE (SUC cnt) sched)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
    (?extra. FLAT (TAKE k ess) =
      gas_events_block (F-e) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
        (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
    (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      gas_events_block (F-e) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
        (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
      u.vs_gas_readings = tail /\
      trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
        (be with vs_gas_readings := FLAT kgss ++ tail)) =
        ZIP (FLAT (TAKE k ks),FLAT kgss) /\
      (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail') =
            OK (u with vs_gas_readings := tail') /\
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (mk_asm "rows") >>
  irule dft_packet_native_row_replay >> simp[] >>
  qexists `ms` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `q < LENGTH xs` by decide_tac >>
      asm "rows" (qspec_then `q` mp_tac) >>
      simp[] >> metis_tac[]) >>
  match_mp_tac dft_packet_return_row_supply >>
  simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `q < LENGTH xs` by decide_tac >>
  qpat_x_assum `!q. q < LENGTH xs /\ _ ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >>
  rpt (goal_assum $ drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
   EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
   EL q ks = AK ((e,(EL q xs).inst_id)::a)` by
    (asm "rows" (qspec_then `q` mp_tac) >> simp[]) >>
  qpat_x_assum `!csf. lookup_function _ _ = _ ==> _` drule >>
  strip_tac >> gvs[] >> metis_tac[]
QED
