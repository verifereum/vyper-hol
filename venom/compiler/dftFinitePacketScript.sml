Theory dftFinitePacket
Ancestors
  dftGasInvCrossingProbe dftGasFromListTraceDefs dftRunRel dftGasOracleDefs
  o1PassContract frameJointTransition unitMemInv list rich_list
  dftGasFromListRestore dftGasToListReplay gasEvents finite_map pred_set
  o1SafeUpto dftGasInvForwardActive stepWriteFootprintBase
  dftFinitePacketReachability dftGasFromListLookup dftContractGas
  dftPacketRootedAlignment dftPacketRefinementBoundary
  dftPacketNativeContinuation dftPacketNativeSlice dftPacketCalleeAlignment
  dftPacketClosedRowNative dftPacketEntryReplay dftPacketFillingBoundary
  o1ScheduleDecompHelpers dftPacketKeyMap dftPacketKeySubstitution dftPacketSlotRefine dftPacketCommonOracle
  dftPacketReturnLocal dftPacketOrdinaryTrace dftPacketSuccessorObservation
  dftGasToListReachBoundary
  dftPacketPseudoNextClauses[qualified,ignore_grammar]
  dftPacketBlockEdgeClauses[qualified,ignore_grammar]
  dftPacketReturnEdgeAssembly[qualified,ignore_grammar]
  dftPacketPreterminalNativeAgreement[qualified,ignore_grammar]
  dftPacketSuccessfulTerminalRow[qualified,ignore_grammar]
  dftPacketPreterminalReadings[qualified,ignore_grammar] dftPacketCallReplayJoin[qualified,ignore_grammar]
  dftPacketCallRecordJoin[qualified,ignore_grammar] o1PassLift[qualified,ignore_grammar]
  dftPacketCallUpdate[qualified,ignore_grammar]
  dftPacketCallRootConservation[qualified,ignore_grammar]
  dftPacketFirstBodyObservation dftPacketPreterminalGeometry

(* Retained native DFT packet and the semantic suspended callers. *)
Definition dft_focus_packet_rel_def:
  dft_focus_packet_rel (N:num) (C7:venom_context) C8 (root_sf:ir_function) (root_tf:ir_function)
    (root_entry:venom_state) packet
    (acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab : (((num # num) list # num), bytes32 option list list) fmap)
    (es_tab : (((num # num) list # num), (string # num) list list) fmap)
    (ks_tab : (((num # num) list # num), gas_event list list) fmap)
    rooted_eval p d q8 raw_slots sites unused <=>
    ?j obs AM AE AK row_eval plan_eval call_setup plan_ok levels_ok
      stk PG G tn fn inst st oms om hs h.
      packet = (j,obs) /\
      q8 = JointConfig stk PG G tn fn inst st oms om hs h /\
      raw_slots = AM [] /\ sites = AE [] /\ unused = st.vs_gas_readings /\
      (?nm lbl.
        C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
        lookup_function nm C7.ctx_functions = SOME root_sf /\
        lookup_function nm C8.ctx_functions = SOME root_tf /\
        fn_entry_label root_sf = SOME lbl /\
        root_entry.vs_prev_bb = NONE /\
        root_entry.vs_current_bb = lbl /\ root_entry.vs_inst_idx = 0) /\
      LENGTH stk = LENGTH p /\
      (!k. k < LENGTH p ==>
        ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
          a = DROP (SUC k) p /\ (e,cid) = EL k p /\
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
          FLOOKUP calls (a,e,cid) =
            SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
          (EL k stk).cf_fn = tf /\
          (EL k stk).cf_state = b0 /\
          (EL k stk).cf_inst.inst_id = cid /\
          (EL k stk).cf_inst.inst_opcode = INVOKE /\
          active_inst tf (EL k stk).cf_inst b0) /\
    LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
    LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
    o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
    MEM root_sf C7.ctx_functions /\ root_tf = dft_fn root_sf /\
    dft_fn_rel root_sf root_tf /\
    strict_dom_vars_defined root_sf root_entry /\
    fn_reachable root_sf root_entry.vs_current_bb /\
    ctx_labels_bound C7 root_entry.vs_labels /\
    ctx_labels_bound C8 root_entry.vs_labels /\
    j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) /\
    EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
      ((p,d,inst.inst_id),fn,inst,st) /\
    obs = dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry)) /\
    LENGTH obs <= LENGTH root_entry.vs_gas_readings /\
      AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
      AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
      AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
      root_entry.vs_gas_readings = MAP SND obs ++ st.vs_gas_readings /\
      ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (AK []) /\
      LENGTH (AM []) = LENGTH (AE []) /\
      LENGTH (AM []) = LENGTH (AK []) /\
      PERM (MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs /\
      FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\
      FDOM blocks = FDOM ks_tab /\
      (?order. FLOOKUP acts [] =
        SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
      (* Activation domains and actual order, retaining children after pop. *)
      (!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
        MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
        inc = (case a of [] => 0 | (e,cid)::parent => e) /\
        order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
        (!e. MEM e order <=> (a,e) IN FDOM blocks) /\
        (res = NONE <=> nrest = NONE) /\
        (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
        (!e cid parent. a = (e,cid)::parent ==>
          ?q h b0 done_at_call ret.
            FLOOKUP calls (parent,e,cid) =
              SOME (q,h,b0,done_at_call,entry,ret))) /\
      (* Every block is an actual first post-PHI visit, not a guessed entry. *)
      (!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest)
        ==>
        ?sf tf inc entry order res nrest sp.
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
          MEM e order /\ e <= N /\ h0 <= j /\
          lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
          lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
          lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb /\
          bt.bb_label = bb.bb_label /\
          bb.bb_instructions = ps ++ xs /\
          bt.bb_instructions = ps ++ ys /\
          EVERY (\x. is_pseudo x.inst_opcode) ps /\
          EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
          EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
          EVERY inst_shape_ok bb.bb_instructions /\
          LENGTH xs = LENGTH ys /\
          PERM row_order (COUNT_LIST (LENGTH xs)) /\
          LIST_REL (\q y. q < LENGTH xs /\
            y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y)
            row_order ys /\
          strict_dom_vars_defined sf in_state /\
          fn_reachable sf in_state.vs_current_bb /\
          ctx_labels_bound C7 in_state.vs_labels /\
          ctx_labels_bound C8 in_state.vs_labels /\
          eval_phis in_state bt.bb_instructions = OK sp /\
          EL h0 (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
            ((a,e,(EL (phi_prefix_length bt.bb_instructions)
              bt.bb_instructions).inst_id),tf,
              EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
              sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
          (if e = SUC inc then in_state = entry else
            ?pb pt pps pxs pys prho pin ph pbe pc (pr:num) pu.
              FLOOKUP blocks (a,e-1) =
                SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK in_state,T,SOME pu)
              /\ ~in_state.vs_halted) /\
          count <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
          (case body_entry of
            NONE => a = p /\ e = d /\ count = 0 /\ front = OK st /\
              FLOOKUP ms_tab (a,e) = SOME [] /\
              FLOOKUP es_tab (a,e) = SOME [] /\
              FLOOKUP ks_tab (a,e) = SOME []
          | SOME (be,hbe) =>
              hbe <= j /\ be.vs_inst_idx = LENGTH ps /\
              be.vs_current_bb = bb.bb_label /\
              dft_remaining_inv sf bb xs be /\
              EL hbe (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
                ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
              FOLDR (dft_exec_cons (N-e) C8) OK
                (DROP (phi_prefix_length bt.bb_instructions) ps)
                (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
              (!F. N <= F ==>
                FOLDR (dft_exec_cons (F-e) C8) OK (TAKE count ys) be = front) /\
              (closed ==> count = LENGTH ys /\ terminates front /\
                (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==>
                  brest = SOME v.vs_gas_readings))) /\
          (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
          (e = LAST order ==>
            res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
      (* Current activation and actual current instruction determine the cursor. *)
      (?sf inc entry order bb bt ps xs ys rho in_state h0 body_entry count.
        FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
        LAST order = d /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,OK st,F,NONE) /\
        lookup_block st.vs_current_bb fn.fn_blocks = SOME bt /\
        get_instruction bt st.vs_inst_idx = SOME inst /\
        (case body_entry of
          NONE => phi_prefix_length bt.bb_instructions <= st.vs_inst_idx /\
            st.vs_inst_idx < LENGTH ps /\ count = 0 /\
            FOLDR (dft_exec_cons (N-d) C8) OK
              (DROP (phi_prefix_length bt.bb_instructions)
                (TAKE st.vs_inst_idx ps))
              ((case eval_phis in_state bt.bb_instructions of
                OK sp => sp | other => in_state)
                with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK st
        | SOME (be,hbe) => st.vs_inst_idx = LENGTH ps + count /\
            count < LENGTH ys /\ inst = EL count ys)) /\
      (* Call records have immutable actual visit/setup/return fields. *)
      (!a e cid q h b0 done_at_call child_entry ret.
        FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
        ?sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
         be hbe count front closed brest csf ctf child_order child_res child_rest
         c nm ops args.
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
          FLOOKUP blocks (a,e) =
            SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
          q < LENGTH xs /\ c = EL q xs /\
          c.inst_id = cid /\ c.inst_opcode = INVOKE /\
          h < j /\ EL h (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
            ((a,e,cid),tf,c,b0) /\
          LENGTH ps <= b0.vs_inst_idx /\
          get_instruction bt b0.vs_inst_idx = SOME c /\
          (!F. N <= F ==>
            FOLDR (dft_exec_cons (F-e) C8) OK
              (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
          done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\
          ~MEM q done_at_call /\
          FLOOKUP acts ((e,cid)::a) =
            SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
          decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C8.ctx_functions = SOME ctf /\
          eval_operands ops b0 = SOME args /\
          setup_callee ctf args b0 = SOME child_entry /\
          (case ret of
            NONE => child_res = NONE /\
              MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
          | SOME (ir,child_out,caller_post) =>
              child_res = SOME (IntRet ir child_out) /\
              bind_outputs c.inst_outputs ir.iret_values
                (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
              h + SUC (LENGTH (dftGasFromListTraceDefs$trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) <= j /\
              MEM q (TAKE count rho))) /\
      (* Every live parent is suspended at its child's immutable call record. *)
      (!k. k < LENGTH p ==>
        ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
         q h b0 done_at_call child_entry cid e a.
          a = DROP (SUC k) p /\ (e,cid) = EL k p /\
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
          LAST order = e /\
          FLOOKUP blocks (a,e) =
            SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
          FLOOKUP calls (a,e,cid) =
            SOME (q,h,b0,done_at_call,child_entry,NONE) /\
          done_at_call = TAKE count rho /\
          b0.vs_inst_idx = LENGTH ps + count /\
          get_instruction bt b0.vs_inst_idx = SOME (EL q xs))

(* Literal plan evaluators; inclusive supplier proof is pending. *)
      /\ row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan =
      GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE)))

(* Row replay, historical caller agreement and closed packets. *)
      /\ (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest
            ms ess ks.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
        FLOOKUP ms_tab (a,e) = SOME ms /\
        FLOOKUP es_tab (a,e) = SOME ess /\
        FLOOKUP ks_tab (a,e) = SOME ks ==>
        LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
        LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
        LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
        ALL_DISTINCT (FLAT ks) /\
        (!sf tf inc entry order res nrest.
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
          (!q. q < LENGTH xs ==>
            ((EL q xs).inst_opcode = GAS ==>
              EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
              EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
              EL q ks = [(a,e,(EL q xs).inst_id)]) /\
            ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
              EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
            ((EL q xs).inst_opcode = INVOKE ==>
              (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
                NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
              | SOME call =>
                  EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
                  EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
                  EL q ks = AK ((e,(EL q xs).inst_id)::a)))) /\
          (* U retains whole-tail replay and unconditional event coverage. *)
          (!F k kgss tail.
            N <= F /\ k <= LENGTH xs /\
            EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
            (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==>
              MEM q (TAKE count rho)) /\
            LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
              (TAKE k ms) kgss ==>
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
              dftGasFromListTraceDefs$trace_gas (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
                (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
                (be with vs_gas_readings := FLAT kgss ++ tail)) =
                ZIP (FLAT (TAKE k ks),FLAT kgss) /\
              (!tail'.
                FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
                  (be with vs_gas_readings := FLAT kgss ++ tail') =
                    OK (u with vs_gas_readings := tail') /\
                gas_events_block (F-e) C7 sf.fn_name
                  <|bb_label := be.vs_current_bb; bb_instructions :=
                    REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
                  (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))))))
      /\ (!a e cid q h b0 done_at_call child_entry ret
            bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
        FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
        FLOOKUP ms_tab (a,e) = SOME ms ==>
        (* Q remains for returned calls as well as suspended calls. *)
        !F kgss tail u.
          N <= F /\
          LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
            (TAKE q ms) kgss /\
          FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
            (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
          (!op. MEM op (EL q xs).inst_operands ==>
            eval_operand op u = eval_operand op b0) /\
          (!callee args.
            setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
            setup_callee callee args b0))
      /\ (!a e sf tf inc entry order res nrest
            bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
        FLOOKUP ms_tab (a,e) = SOME ms /\
        FLOOKUP es_tab (a,e) = SOME ess /\
        FLOOKUP ks_tab (a,e) = SOME ks ==>
        terminates r8 /\
        PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
        (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
          EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
        (!F. N <= F ==>
          FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
          (!gs tail.
            LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
            (?extra. FLAT ess =
              gas_events_block (F-e) C7 sf.fn_name
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail) ++ extra) /\
            ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
                (be with vs_gas_readings := gs ++ tail))) ==>
              terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)) /\
              dft_res_rel
                (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail)))
                (restore_result [] r8) /\
              (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
                gas_events_block (F-e) C7 sf.fn_name
                  <|bb_label := be.vs_current_bb; bb_instructions :=
                    REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                  (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
                residual_result tail r8
                  (FOLDR (dft_exec_cons (F-e) C7) OK xs
                    (be with vs_gas_readings := gs ++ tail)))) /\
            (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                    (be with vs_gas_readings := gs ++ tail) = OK v \/
                  ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                    (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
              dftGasFromListTraceDefs$trace_gas (dftGasFromListTraceDefs$trace_block a e (F-e) C7 sf
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)))))
      /\ (!a sf tf inc entry order r8 u0.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
        terminates r8 /\
        LENGTH (AM a) = LENGTH (AE a) /\ LENGTH (AM a) = LENGTH (AK a) /\
        PERM (MAP THE (FILTER IS_SOME (AM a)) ++ u0) entry.vs_gas_readings /\
        (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
          EVERY IS_SOME (AM a) /\ u0 = v.vs_gas_readings) /\
        (!F. N <= F ==>
          run_blocks (F-inc) C8 tf entry = r8 /\
          (!gs tail.
            LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM a) gs ==>
            (?extra. AE a = gas_events_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
            ((?f. terminates (run_blocks f C7 sf
                (entry with vs_gas_readings := gs ++ tail))) ==>
              terminates (run_blocks (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)) /\
              dft_res_rel
                (restore_result [] (run_blocks (F-inc) C7 sf
                  (entry with vs_gas_readings := gs ++ tail)))
                (restore_result [] r8) /\
              (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
                gas_events_blocks (F-inc) C7 sf
                  (entry with vs_gas_readings := gs ++ tail) = AE a /\
                residual_result tail r8
                  (run_blocks (F-inc) C7 sf
                    (entry with vs_gas_readings := gs ++ tail)))) /\
            (!v. (run_blocks (F-inc) C7 sf
                    (entry with vs_gas_readings := gs ++ tail) = OK v \/
                  ?ir. run_blocks (F-inc) C7 sf
                    (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
              dftGasFromListTraceDefs$trace_gas (dftGasFromListTraceDefs$trace_blocks a inc (F-inc) C7 sf
                (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs)))))
      /\ (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) ==>
        !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
          MEM q (TAKE count rho) ==>
          ?h b0 done_at_call child_entry ir child_out caller_post.
            FLOOKUP calls (a,e,(EL q xs).inst_id) =
              SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post)))
      /\ (!bb bt ps xs ys rho in_state h0 be hbe count sf inc entry order.
        FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK st,F,NONE) /\
        inv_memory_observation inst.inst_opcode ==>
        EL (EL count rho) xs = inst /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count rho) xs) /\
        (!q. q < EL count rho /\ (EL q xs).inst_opcode = INVOKE ==>
          MEM q (TAKE count rho)))

(* Rooted cuts are fixed before F/gs/tail, from the same retained tables. *)
      /\ (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
            body_entry count front closed brest q z.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        ((IS_SOME body_entry /\ q < LENGTH xs /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
          (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
            MEM r (TAKE count rho))) \/
         (body_entry = NONE /\ a = p /\ e = d /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE st.vs_inst_idx ps)))
        ==>
        ?cuts levels Mcut Ecut Kcut mr er kr.
          MAP (\(ai,ds,ei,qi,zi). ai) cuts =
            REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
          LENGTH cuts = LENGTH levels /\
          (!i ai ds ei qi zi.
            i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
            ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
              ini hi bei counti fronti closedi resti later.
              FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
              FLOOKUP blocks (ai,ei) =
                SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
              orderi = ds ++ ei::later /\
              (if SUC i = LENGTH cuts then
                ai = a /\ ei = e /\ qi = q /\ zi = z
              else
                ?cid h b0 done_at_call child_entry ret.
                  EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                  FLOOKUP calls (ai,ei,cid) =
                    SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                  qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                  zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                  EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                  (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                    MEM r done_at_call)) /\
              EL i levels =
                (sfi,
                 MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
                   (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                     (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++
                   [(bbi,ei,zi)],
                 if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
          Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
            FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
            FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
          Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
            FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
            FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
          Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
            FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
            FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
          AM [] = Mcut ++ mr /\ AE [] = Ecut ++ er /\ AK [] = Kcut ++ kr /\
          LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
          (!F gs tail.
            N <= F /\
            LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
            levels_ok F C7 levels
              (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
              (MAP (\(ai,ds,ei,qi,zi).
                case THE (FLOOKUP acts ai) of
                  (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
              root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
            (?extra. Ecut = FST (rooted_eval F C7 levels
              (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
            (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
              OK u =>
                FST (rooted_eval F C7 levels
                  (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                u.vs_gas_readings = tail /\
                (?before after.
                  dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                    before ++ [((a,e,(EL (LENGTH z)
                      (DROP (phi_prefix_length bb.bb_instructions)
                        bb.bb_instructions)).inst_id),sf,
                      EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                        bb.bb_instructions),u)] ++ after /\
                  dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                (!tail'. rooted_eval F C7 levels
                  (root_entry with vs_gas_readings := gs ++ tail') =
                    (Ecut,OK (u with vs_gas_readings := tail'))) /\
                (body_entry = NONE ==>
                  u with vs_gas_readings := st.vs_gas_readings = st) /\
                (a = p /\ e = d /\ IS_SOME body_entry /\
                 inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                  (!op. MEM op inst.inst_operands ==>
                    eval_operand op u = eval_operand op st) /\
                  u.vs_initial_fmp = st.vs_initial_fmp)
            | stopped =>
                run_blocks F C7 root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                gas_events_blocks F C7 root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                    FST (rooted_eval F C7 levels
                      (root_entry with vs_gas_readings := gs ++ tail)))))
End

Theorem dft_packet_cut_mem_inv[local]:
  !C root gs tail u slots n M fn inst.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots gs /\
    LENGTH slots < n /\ u.vs_gas_readings = tail /\
    raw_reachable (root with vs_gas_readings := gs ++ tail) C fn inst u /\
    mem_inv (\ctx f i s.
      gas_cut n (root with vs_gas_readings := gs ++ tail) s ==> M ctx f i s)
      C (root with vs_gas_readings := gs ++ tail) ==>
    M C fn inst u
Proof
  rpt strip_tac >>
  `LENGTH gs = LENGTH slots` by metis_tac[LIST_REL_LENGTH] >>
  `gas_cut n (root with vs_gas_readings := gs ++ tail) u` by
    simp[gas_cut_def] >>
  gvs[mem_inv_raw_reachable] >> metis_tac[]
QED

Theorem dft_packet_active_block:
  wf_function sf /\ active_inst sf inst u /\
  lookup_block lbl sf.fn_blocks = SOME bb /\ MEM inst bb.bb_instructions ==>
  u.vs_current_bb = bb.bb_label
Proof
  rpt strip_tac >>
  gvs[contextCodegenRelTheory.active_inst_def] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  metis_tac[venomWfPropsTheory.wf_function_instruction_block, MEM_EL]
QED

Theorem dft_packet_cut_instruction:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ q < LENGTH xs /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs ==>
  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) =
    EL q xs
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (gvs[EVERY_MEM] >> metis_tac[venomInstTheory.is_pseudo_def]) >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length ps` by
    metis_tac[dftIndexedExecTheory.dft_phi_prefix_append] >>
  `phi_prefix_length ps <= LENGTH ps` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  simp[DROP_APPEND, LENGTH_TAKE, EL_APPEND_EQN] >>
  `phi_prefix_length ps - LENGTH ps = 0` by decide_tac >> simp[]
QED

Theorem dft_packet_source_projection:
  (!N C7 C8 root_sf root_tf root_entry packet acts blocks calls
      ms_tab es_tab ks_tab rooted_eval p d stk PG G tn fn inst s oms om hs h.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
    (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
      inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s ==>
    ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z.
      FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
      LAST order = d /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE) /\
      q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
      (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE count rho))) /\
  (!C nm root lbl entry key fn inst s F.
    C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME root /\
    fn_entry_label root = SOME lbl /\ entry.vs_prev_bb = NONE /\
    entry.vs_current_bb = lbl /\ entry.vs_inst_idx = 0 /\
    MEM (key,fn,inst,s) (dftGasFromListTraceDefs$trace_blocks [] 0 F C root entry)
    ==> raw_reachable entry C fn inst s) ==>
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls
    ms_tab es_tab ks_tab rooted_eval p d stk PG G tn fn inst s oms om hs h cpl.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused ==>
    ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
       inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s ==>
      ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z
        cuts levels Mcut Ecut.
        FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
        LAST order = d /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE) /\
        q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
          MEM r (TAKE count rho)) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid call_h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        LENGTH Mcut = LENGTH Ecut /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            C7 (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom C7 sf inst u /\
          ~in_revert_forward sf u /\
          (inv_memory_observation inst.inst_opcode ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
            u.vs_initial_fmp = s.vs_initial_fmp)))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "cursor") (mk_asm "reach")) >>
  rpt gen_tac >> strip_tac >> disch_tac >>
  asm "cursor" drule >>
  (impl_tac >- simp[]) >> strip_tac >>
  asm_x "cursor" kall_tac >>
  rename1 `FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,SOME(be,hbe),done,OK s,F,NONE)` >>
  qexistsl [`sf`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,`schedule`,
    `in_state`,`h0`,`be`,`hbe`,`done`,`q`,`z`] >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  pure_rewrite_tac [dft_focus_packet_rel_def] >> strip_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac [joint_config_11] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  qpat_x_assum
    `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
       body_entry count front closed brest q z. _` rev_drule >>
  disch_then rev_drule >>
  disch_then (qspecl_then [`q`,`z`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`] >>
  ntac 11 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `!i ai ds ei qi zi. _` mp_tac >>
      pure_rewrite_tac [pairTheory.pair_CASE_def] >>
      simp_tac bool_ss []) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`,`n`,`u`] >> strip_tac >>
  qpat_x_assum `!F gs tail. _` (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `rooted_eval fuel _ _ _ = (Ecut,OK u)`
    (fn th => pure_rewrite_tac [th]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
    rev_drule >> strip_tac >>
  ntac 2 (qpat_x_assum `FLOOKUP acts p = SOME _` mp_tac >>
    asm_simp_tac (srw_ss()) [] >>
    disch_then (map_every SUBST_ALL_TAC o CONJUNCTS)) >>
  qpat_x_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  rename1 `static_mem_ok cpl.cp_max_static_eom C7 sf inst u` >>
  rename1 `z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` >>
  rename1 `lookup_block st.vs_current_bb tf.fn_blocks = SOME bt` >>
  drule_all dft_packet_cut_instruction >> disch_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = _ ==> _` (qspec_then `p` drule) >> strip_tac >>
  `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
      bb.bb_instructions) = inst` by (bossLib.simp []) >>
  `MEM ((p,d,inst.inst_id),sf,inst,u)
    (dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf
      (root_entry with vs_gas_readings := gs ++ tail))` by
    (qpat_x_assum `dftGasFromListTraceDefs$trace_blocks [] 0 fuel _ _ _ = _`
      (fn th => pure_rewrite_tac [th]) >> simp[]) >>
  `raw_reachable (root_entry with vs_gas_readings := gs ++ tail) C7 sf inst u` by
    (asm "reach" irule >> simp[] >>
     qexistsl [`fuel`,`(p,d,inst.inst_id)`] >> simp[]) >>
  conj_tac
  >- (drule_all dft_packet_cut_mem_inv >> simp[]) >>
  `active_inst sf inst u` by
    (qpat_assum `raw_reachable _ C7 sf inst u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[raw_reachable_active]) >>
  `wf_function sf` by
    (qpat_assum `dft_fn_rel sf tf` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[dft_fn_rel_def]) >>
  `MEM inst bb.bb_instructions` by
    (qpat_x_assum `q < LENGTH xs` mp_tac >>
     qpat_x_assum `EL q xs = inst` mp_tac >>
     qpat_x_assum `bb.bb_instructions = ps ++ xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[EL_MEM, MEM_APPEND]) >>
  `u.vs_current_bb = bb.bb_label` by
    (qpat_assum `wf_function sf` mp_tac >>
     qpat_assum `active_inst sf inst u` mp_tac >>
     qpat_assum `lookup_block _ sf.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `MEM inst bb.bb_instructions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[dft_packet_active_block]) >>
  `st.vs_current_bb = bt.bb_label` by
    (qpat_assum `lookup_block st.vs_current_bb tf.fn_blocks = SOME bt`
      (ACCEPT_TAC o SYM o cj 2 o
       MATCH_MP simplifyCfgDefsTheory.lookup_block_member_label)) >>
  `active_inst tf inst st` by
    (simp[contextCodegenRelTheory.active_inst_def] >>
     qexists_tac `bt` >>
     qpat_x_assum `get_instruction bt _ = SOME inst` mp_tac >>
     simp_tac (srw_ss()) [venomInstTheory.get_instruction_def] >>
     strip_tac >>
     qpat_assum `lookup_block bb.bb_label tf.fn_blocks = SOME bt` mp_tac >>
     qpat_assum `tf = dft_fn sf` mp_tac >>
     qpat_assum `st.vs_current_bb = bt.bb_label` mp_tac >>
     qpat_assum `bt.bb_label = bb.bb_label` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[simplifyCfgDefsTheory.lookup_block_member_label]) >>
  qpat_x_assum `o1_ctx_shape C7` mp_tac >>
  qpat_x_assum `MEM sf C7.ctx_functions` mp_tac >>
  qpat_x_assum `tf = dft_fn sf` mp_tac >>
  qpat_x_assum `dft_fn_rel sf tf` mp_tac >>
  qpat_x_assum `active_inst sf inst u` mp_tac >>
  qpat_x_assum `active_inst tf inst st` mp_tac >>
  qpat_x_assum `u.vs_current_bb = bb.bb_label` mp_tac >>
  qpat_x_assum `st.vs_current_bb = bt.bb_label` mp_tac >>
  qpat_x_assum `bt.bb_label = bb.bb_label` mp_tac >>
  qpat_x_assum `(_ \/ _) /\ ~in_revert_forward tf st` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[inv_forward_active]
QED
Theorem dft_packet_guard_from_block[local]:
  !xs i. from_block xs i /\
    (inv_memory_observation i.inst_opcode \/ is_fallible i \/
     i.inst_opcode = INVOKE) ==> MEM i xs
Proof
  rw[dftStructuralTheory.from_block_def] >>
  Cases_on `j.inst_operands` >>
  gvs[dftDefsTheory.flip_operands_def] >>
  Cases_on `t` >> gvs[dftDefsTheory.flip_operands_def] >>
  Cases_on `t'` >> gvs[dftDefsTheory.flip_operands_def] >>
  Cases_on `j.inst_opcode` >>
  gvs[inv_memory_observation_def, dftDefsTheory.is_fallible_def,
      venomEffectsTheory.opcode_fail_class_def, dftDefsTheory.is_flippable_def,
      venomEffectsTheory.is_commutative_def, passSharedDefsTheory.is_comparator_def,
      passSharedDefsTheory.flip_comparison_opcode_def]
QED

Theorem dft_packet_guard_not_pseudo[local]:
  !i. (inv_memory_observation i.inst_opcode \/ is_fallible i \/
       i.inst_opcode = INVOKE) ==> ~is_pseudo i.inst_opcode
Proof
  gen_tac >> Cases_on `i.inst_opcode` >>
  simp[inv_memory_observation_def, dftDefsTheory.is_fallible_def,
       venomEffectsTheory.opcode_fail_class_def, venomInstTheory.is_pseudo_def]
QED

Theorem dft_packet_invoke_fallible_order[local]:
  !x y. x.inst_opcode = INVOKE /\ (is_fallible y \/ y.inst_opcode = INVOKE) ==>
    ~dft_abort_compatible x.inst_opcode y.inst_opcode \/ dft_must_order x y
Proof
  rpt gen_tac >> Cases_on `y.inst_opcode` >>
  simp[dftDefsTheory.is_fallible_def, venomEffectsTheory.opcode_fail_class_def,
       dftDefsTheory.dft_abort_compatible_def, dftDefsTheory.dft_abort_kind_def,
       dftScheduleOrderTheory.dft_must_order_def,
       venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def, venomInstTheory.is_terminator_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_packet_id_before_take[local]:
  !l k a. ALL_DISTINCT l /\ k < LENGTH l /\
    id_before l a (EL k l) ==> MEM a (TAKE k l)
Proof
  rpt strip_tac >>
  gvs[dftScheduleOrderTheory.id_before_def] >>
  `j = k` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >>
  gvs[] >> simp[MEM_EL] >> qexists_tac `i` >> simp[EL_TAKE]
QED

(* Both guarded cursor interfaces use the same schedule argument. *)
Theorem dft_packet_ordered_schedule_predecessors[local]:
  !sf tf bb bt ps xs ys rho count q.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  count < LENGTH ys /\ q = EL count rho /\ EL q xs = EL count ys /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
    ~dft_abort_compatible (EL r xs).inst_opcode (EL q xs).inst_opcode \/
    dft_must_order (EL r xs) (EL q xs)) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
    MEM r (TAKE count rho))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `PERM sched (COUNT_LIST (LENGTH xs))` >>
  rename1 `q = EL pos sched` >>
  `wf_function sf` by fs[dftRunRelTheory.dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `q < LENGTH xs` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = xs` by
    (`FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
      FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) ps = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
       simp[FILTER_EQ_ID, FILTER_EQ_NIL] >>
     simp[FILTER_APPEND_DISTRIB]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by gvs[ALL_DISTINCT_APPEND] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) ys)` by
    (qpat_x_assum `dft_block_rel bb bt`
      (strip_assume_tac o REWRITE_RULE [dftScheduleOrderTheory.dft_block_rel_def]) >>
     fs[] >> metis_tac[sortingTheory.ALL_DISTINCT_PERM]) >>
  conj_tac
  >- (rewrite_tac[EVERY_EL] >> qx_gen_tac `n` >> disch_tac >>
      `n < q /\ n < LENGTH xs` by (gvs[LENGTH_TAKE] >> decide_tac) >>
      simp[EL_TAKE] >> irule dft_wf_order_nonterminator >>
      qexistsl_tac [`bb`, `sf`, `EL q xs`] >> simp[] >>
      conj_tac >- metis_tac[MEM_EL, MEM_APPEND] >>
      irule id_before_append_right >>
      simp[dftScheduleOrderTheory.id_before_def] >>
      qexistsl_tac [`n`, `q`] >> simp[EL_MAP]) >>
  suspend "calls"
QED

Resume dft_packet_ordered_schedule_predecessors[calls]:
  rpt strip_tac >>
  `r < LENGTH xs` by decide_tac >>
  `MEM (EL r xs) bb.bb_instructions /\ MEM (EL q xs) bb.bb_instructions` by
    metis_tac[MEM_EL, MEM_APPEND] >>
  `~is_pseudo (EL r xs).inst_opcode /\ ~is_pseudo (EL q xs).inst_opcode` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions)
     (EL r xs).inst_id (EL q xs).inst_id` by
    (simp[] >> irule id_before_append_right >>
     simp[dftScheduleOrderTheory.id_before_def] >>
     qexistsl_tac [`r`, `q`] >> simp[EL_MAP]) >>
  `id_before (MAP (\i. i.inst_id) bt.bb_instructions)
     (EL r xs).inst_id (EL q xs).inst_id` by
    (Cases_on `dft_abort_compatible (EL r xs).inst_opcode (EL q xs).inst_opcode`
     >- (`dft_must_order (EL r xs) (EL q xs)` by
           metis_tac[] >>
         qpat_x_assum `dft_block_rel bb bt`
           (strip_assume_tac o REWRITE_RULE [dftScheduleOrderTheory.dft_block_rel_def]) >>
         fs[] >> irule id_before_append_right >> metis_tac[]) >>
     metis_tac[]) >>
  `~MEM (EL r xs).inst_id (MAP (\i. i.inst_id) ps) /\
   ~MEM (EL q xs).inst_id (MAP (\i. i.inst_id) ps)` by
    (`MEM (EL r xs).inst_id (MAP (\i. i.inst_id) xs) /\
      MEM (EL q xs).inst_id (MAP (\i. i.inst_id) xs)` by
       (conj_tac >> simp[MEM_MAP] >> metis_tac[MEM_EL]) >>
     qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
     asm_rewrite_tac[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) ys) (EL r xs).inst_id (EL q xs).inst_id` by
    (qpat_x_assum `id_before (MAP _ bt.bb_instructions) _ _` mp_tac >>
     gvs[dftScheduleOrderTheory.id_before_append_suffix]) >>
  `MEM (EL r xs).inst_id (MAP (\i. i.inst_id) (TAKE pos ys))` by
    (rewrite_tac[MAP_TAKE] >> irule dft_packet_id_before_take >>
     simp[EL_MAP] >> metis_tac[]) >>
  `?k. k < pos /\ (EL k ys).inst_id = (EL r xs).inst_id` by
    (qpat_x_assum `MEM _ (MAP _ (TAKE pos ys))` mp_tac >>
     simp[MEM_MAP, MEM_EL, EL_TAKE] >> (metis_tac [listTheory.EL_TAKE])) >>
  `k < LENGTH ys` by decide_tac >>
  qpat_x_assum `LIST_REL _ sched ys` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
  strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  `EL k sched = r` by
    (fs[EL_ALL_DISTINCT_EL_EQ] >> metis_tac[EL_MAP]) >>
  simp[MEM_EL] >> qexists_tac `k` >> simp[EL_TAKE]
QED

Finalise dft_packet_ordered_schedule_predecessors

Theorem dft_packet_schedule_predecessors:
  !sf tf bb bt ps xs ys rho count q.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  count < LENGTH ys /\ q = EL count rho /\ EL q xs = EL count ys /\
  (is_fallible (EL q xs) \/ (EL q xs).inst_opcode = INVOKE) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
    MEM r (TAKE count rho))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule dft_packet_ordered_schedule_predecessors >>
  rpt (first_assum (irule_at Any)) >>
  metis_tac[dft_packet_invoke_fallible_order]
QED

Theorem dft_packet_memory_schedule_predecessors:
  !sf tf bb bt ps xs ys rho pos q.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  pos < LENGTH ys /\ q = EL pos rho /\ EL q xs = EL pos ys /\
  inv_memory_observation (EL q xs).inst_opcode ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
    MEM r (TAKE pos rho))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule dft_packet_ordered_schedule_predecessors >>
  rpt (first_assum (irule_at Any)) >>
  metis_tac[dft_packet_invoke_memory_order]
QED

Theorem dft_packet_next_memory_eligible:
  !sf tf bb bt ps xs ys rho count q.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  SUC count < LENGTH ys /\ q = EL (SUC count) rho /\
  EL q xs = EL (SUC count) ys /\
  inv_memory_observation (EL q xs).inst_opcode /\
  (EL count ys).inst_opcode <> INVOKE ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
    MEM r (TAKE count rho))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `PERM sched (COUNT_LIST (LENGTH xs))` >>
  rename1 `SUC pos < LENGTH ys` >>
  drule_all dft_packet_memory_schedule_predecessors >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `pos < LENGTH sched /\ pos < LENGTH ys` by
    (fs[LIST_REL_EL_EQN] >> decide_tac) >>
  `from_block [EL (EL pos sched) xs] (EL pos ys)` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `(EL (EL pos sched) xs).inst_opcode <> INVOKE` by
    (strip_tac >>
     qpat_x_assum `from_block _ _` mp_tac >>
     simp[dftStructuralTheory.from_block_def, dftDefsTheory.is_flippable_def,
          venomEffectsTheory.is_commutative_def, passSharedDefsTheory.is_comparator_def,
          venomInstTheory.is_pseudo_def] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `MEM r (TAKE (SUC pos) sched)` by metis_tac[] >>
  gvs[TAKE_SUC_BY_TAKE, MEM_SNOC] >> metis_tac[]
QED

Theorem dft_packet_guarded_cursor_structure:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
    inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s) ==>
  ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    LAST order = d /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    dft_fn_rel sf fn /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
    EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
    LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) rho ys /\
    count < LENGTH ys /\ inst = EL count ys /\
    (inv_memory_observation inst.inst_opcode ==>
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
      (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE count rho)))
Proof
  disch_then (CONJUNCTS_THEN2
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) assume_tac) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `FLOOKUP acts p = _` mp_tac >>
  qpat_x_assum `LAST _ = d` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
  qpat_x_assum `lookup_block st.vs_current_bb _ = _` mp_tac >>
  qpat_x_assum `get_instruction _ _ = _` mp_tac >>
  qpat_x_assum `case body_entry of NONE => _ | SOME v => _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp. _` mp_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `!bb bt ps xs ys rho in_state h0 be hbe count sf inc entry order.
    FLOOKUP acts p = _ /\ FLOOKUP blocks (p,d) = _ /\ inv_memory_observation _ ==> _` mp_tac >>
  qpat_x_assum `(_ \/ _ \/ _) /\ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o SRULE []) >>
  gnvs[] >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` drule >> strip_tac >>
  gnvs[] >> Cases_on `body_entry`
  >- (gvs[] >>
      `~is_pseudo inst.inst_opcode` by metis_tac[dft_packet_guard_not_pseudo] >>
      gvs[venomInstTheory.get_instruction_def, EL_APPEND, EVERY_EL] >>
      metis_tac[]) >>
  PairCases_on `x` >> gvs[] >>
  `count' < LENGTH rho'` by metis_tac[LIST_REL_LENGTH] >>
  qpat_assum `LIST_REL _ rho' ys`
    (mp_tac o SRULE [LIST_REL_EL_EQN]) >> strip_tac >>
  first_x_assum (qspec_then `count'` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `EL (EL count' rho') xs = EL count' ys` by
    metis_tac[dft_packet_guard_from_block, MEM] >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = _ ==> _` drule >> strip_tac >>
  simp[]
QED

Theorem dft_packet_guarded_cursor:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
    inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s) ==>
  ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    LAST order = d /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
      MEM r (TAKE count rho))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule dft_packet_guarded_cursor_structure >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `PERM sched (COUNT_LIST (LENGTH xs))` >>
  rename1 `q = EL pos sched` >>
  qexistsl_tac [`sf`, `inc`, `entry`, `order`, `bb`, `bt`, `ps`, `xs`, `ys`,
    `sched`, `in_state`, `h0`, `be`, `hbe`, `pos`, `q`, `z`] >> simp[] >>
  Cases_on `inv_memory_observation inst.inst_opcode`
  >- metis_tac[] >>
  irule dft_packet_schedule_predecessors >> metis_tac[]
QED

Theorem dft_packet_setup_readings:
  (!callee args.
    setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee args b0) /\
  setup_callee ctf args b0 = SOME child_entry ==>
  setup_callee ctf args u =
    SOME (child_entry with vs_gas_readings := u.vs_gas_readings)
Proof
  strip_tac >>
  first_x_assum (qspecl_then [`ctf`, `args`] mp_tac) >>
  simp[gasOracleReplayTheory.gas_setup_callee] >>
  Cases_on `setup_callee ctf args u` >> simp[] >> strip_tac >>
  drule gasOracleReplayTheory.gas_setup_callee_readings >>
  simp[venomStateTheory.venom_state_component_equality]
QED

Theorem dft_packet_native_row_keys:
  !pre kss s bb.
    pre = DROP s.vs_inst_idx bb.bb_instructions /\
    LIST_REL (\i keys.
      if i.inst_opcode = GAS then keys = [(p,d,i.inst_id)]
      else if i.inst_opcode = INVOKE then T else keys = []) pre kss /\
    (!j st.
      j < LENGTH pre /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE j pre) /\
      FOLDR (dft_exec_cons fuel C) OK (TAKE j pre) s = OK st /\
      (EL j pre).inst_opcode = INVOKE ==>
      (?extra. EL j kss = MAP FST (trace_gas
        (trace_step p d fuel C fn (EL j pre) st)) ++ extra) /\
      (!u. step_inst fuel C (EL j pre) st = OK u ==>
        EL j kss = MAP FST (trace_gas
          (trace_step p d fuel C fn (EL j pre) st)))) ==>
    ?extra. FLAT kss = MAP FST (trace_gas
      (trace_block p d fuel C fn bb s)) ++ extra
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      simp[Once trace_defs, venomInstTheory.get_instruction_def, trace_gas_def]) >>
  namedCases_on `kss` ["", "row rows"] >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `_ = DROP _ _`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  `(?extra. row = MAP FST (visit_gas ((p,d,h.inst_id),fn,h,s) ++
      trace_gas (trace_step p d fuel C fn h s)) ++ extra) /\
   (!u. step_inst fuel C h s = OK u ==>
      row = MAP FST (visit_gas ((p,d,h.inst_id),fn,h,s) ++
        trace_gas (trace_step p d fuel C fn h s)))` by
    (Cases_on `h.inst_opcode = INVOKE`
     >- (qpat_x_assum `!j st. _` (qspecl_then [`0`, `s`] mp_tac) >>
         qpat_x_assum `h::pre = _` (fn th => pure_rewrite_tac[GSYM th]) >>
         simp[visit_gas_def]) >>
     Cases_on `h.inst_opcode = GAS` >>
     gvs[trace_step_noninvoke, visit_gas_def, trace_gas_def]) >>
  Cases_on `step_inst fuel C h s`
  >- suspend "ok"
  >> (`get_instruction bb s.vs_inst_idx = SOME h` by
        simp[venomInstTheory.get_instruction_def] >>
      drule trace_block_visit >> disch_then (fn th => once_rewrite_tac[th]) >>
      simp[dftGasFromListReadingsTheory.trace_gas_cons,
           dftGasFromListReadingsTheory.trace_gas_append,
           dftGasFromListReadingsTheory.trace_gas_nil, MAP_APPEND] >>
      metis_tac[APPEND_ASSOC, MAP_APPEND])
QED

Resume dft_packet_native_row_keys[ok]:
  rename1 `step_inst fuel C h s = OK out` >>
  `row = MAP FST (visit_gas ((p,d,h.inst_id),fn,h,s) ++
      trace_gas (trace_step p d fuel C fn h s))` by metis_tac[] >>
  qpat_x_assum `!u. _` kall_tac >>
  qpat_x_assum `row = _ ++ extra` kall_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[venomInstTheory.get_instruction_def] >>
  Cases_on `is_terminator h.inst_opcode`
  >- (drule trace_block_visit >> disch_then (fn th => once_rewrite_tac[th]) >>
      simp[dftGasFromListReadingsTheory.trace_gas_cons,
           dftGasFromListReadingsTheory.trace_gas_append, MAP_APPEND] >>
      metis_tac[APPEND_ASSOC]) >>
  first_x_assum (qspecl_then [`rows`, `out with vs_inst_idx := SUC s.vs_inst_idx`, `bb`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!j st. _` (qspecl_then [`SUC j`, `st`] mp_tac) >>
      qpat_x_assum `h::pre = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      simp[dftIndexedExecTheory.dft_exec_cons_def]) >>
  strip_tac >>
  drule trace_block_visit >> disch_then (fn th => once_rewrite_tac[th]) >>
  simp[dftGasFromListReadingsTheory.trace_gas_cons,
       dftGasFromListReadingsTheory.trace_gas_append, MAP_APPEND] >>
  metis_tac[APPEND_ASSOC]
QED

Finalise dft_packet_native_row_keys

Theorem dft_packet_return_frame:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  joint_transition C8 (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginResume fuel fn inst s ir child_out caller_post)) q8' ==>
  ?e cid a f rest sf tf inc entry order bb bt ps xs ys rho in_state h0
    be hbe count q call_h b0 done child_entry inst' caller_om oms' caller_h hs'.
    p = (e,cid)::a /\ stk = f::rest /\ LENGTH rest = LENGTH a /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
    LAST order = e /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
    FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,child_entry,NONE) /\
    done = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
    f.cf_fn = tf /\ f.cf_state = b0 /\ f.cf_inst.inst_id = cid /\
    f.cf_inst.inst_opcode = INVOKE /\ f.cf_inst = EL q xs /\
    step_inst fuel C8 inst s = IntRet ir child_out /\
    bind_outputs (EL q xs).inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
    active_inst tf inst' (caller_post with vs_inst_idx := SUC b0.vs_inst_idx) /\
    oms = caller_om::oms' /\ hs = caller_h::hs' /\
    q8' = JointConfig rest f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      tf inst' (caller_post with vs_inst_idx := SUC b0.vs_inst_idx) oms'
      (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs'
      (caller_h ++ [OriginResume fuel fn inst s ir child_out caller_post;
        OriginObserve (OriginSnapshot tf f.cf_params
          (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
          (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) inst'
          (caller_post with vs_inst_idx := SUC b0.vs_inst_idx))])
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  pure_rewrite_tac [joint_transition_return] >> strip_tac >>
  gvs[frameJointTransitionTheory.joint_config_11] >>
  qhdtm_x_assum `dft_focus_packet_rel` mp_tac >>
  pure_rewrite_tac [dft_focus_packet_rel_def] >> strip_tac >>
  `!key tf c b0. MEM (key,tf,c,b0) (trace_blocks [] 0 N C8 root_tf root_entry) ==>
      active_inst tf c b0 /\ wf_function tf` by
    (rpt gen_tac >> disch_tac >>
     `raw_reachable root_entry C8 tf c b0` suffices_by
       (strip_tac >> conj_tac
        >- (drule stepWriteFootprintBaseTheory.raw_reachable_active >> simp[]) >>
        drule raw_reachable_wf >> simp[o1_ctx_shape_wf_functions]) >>
     drule dft_fn_rel_entry_label >> disch_tac >>
     qpat_x_assum `MEM (key,tf,c,b0) _` mp_tac >>
     qpat_x_assum `fn_entry_label root_tf = _` mp_tac >>
     qpat_x_assum `fn_entry_label root_sf = _` mp_tac >>
     qpat_x_assum `C8.ctx_entry = _` mp_tac >>
     qpat_x_assum `lookup_function nm C8.ctx_functions = _` mp_tac >>
     qpat_x_assum `root_entry.vs_prev_bb = _` mp_tac >>
     qpat_x_assum `root_entry.vs_current_bb = _` mp_tac >>
     qpat_x_assum `root_entry.vs_inst_idx = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[dft_packet_trace_raw_reachable]) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==> _` mp_tac >>

  qpat_x_assum `!key tf c b0. _` mp_tac >>
  qpat_x_assum `j < LENGTH _` mp_tac >>
  qpat_x_assum `!k. _ ==> ?sf tf inc entry order q call_h b0 done child_entry e cid a. _ /\ _ /\ _ /\ _ /\ (EL k _).cf_fn = tf /\ _` mp_tac >>
  qpat_x_assum `!k. _ ==> ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q h b0 done child_entry cid e a. _` mp_tac >>
  qpat_x_assum `LENGTH _ = LENGTH p` mp_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  qpat_x_assum `bind_outputs _ _ _ = SOME _` mp_tac >>
  qpat_x_assum `active_inst _ inst' _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt strip_tac >> gvs[frameJointTransitionTheory.joint_config_11] >>
  Cases_on `p` >- gvs[] >>
  qpat_x_assum `!k. _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!k. _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret. _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `call_h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by decide_tac >>
  `MEM ((t,LAST order,f.cf_inst.inst_id),f.cf_fn,EL q xs,f.cf_state)
     (trace_blocks [] 0 N C8 root_tf root_entry)` by metis_tac[EL_MEM] >>
  qpat_x_assum `!key tf c b0. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `active_inst _ (EL q xs) _` mp_tac >>
  qpat_x_assum `active_inst _ f.cf_inst _` mp_tac >>
  qpat_x_assum `wf_function _` mp_tac >>
  qpat_x_assum `bind_outputs _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  drule_all wf_active_lookup >> strip_tac >>
  qpat_x_assum `active_inst _ (EL q xs) _` kall_tac >>
  drule_all wf_active_lookup >> strip_tac >>
  gvs[]
QED

Theorem dft_packet_table_alignment[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  !a e. (a,e) IN FDOM blocks ==>
    LENGTH (FLAT (THE (FLOOKUP ks_tab (a,e)))) =
      LENGTH (FLAT (THE (FLOOKUP ms_tab (a,e))))
Proof
  rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (mp_tac o cj 5) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` drule >> strip_tac >>
  Cases_on `x8`
  >- (qpat_x_assum `case NONE of NONE => _ | SOME v => _` mp_tac >>
      simp[] >> strip_tac >> simp[]) >>
  PairCases_on `x` >>
  Cases_on `FLOOKUP ms_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP es_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP ks_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` drule >> simp[] >> strip_tac >>
  metis_tac[dft_key_map_flat_length]
QED

Theorem dft_packet_block_pair[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
  !a e rows keyrows kv.
    FLOOKUP ms_tab (a,e) = SOME rows /\
    FLOOKUP ks_tab (a,e) = SOME keyrows /\
    MEM kv (ZIP (FLAT keyrows,FLAT rows)) ==>
    MEM kv (ZIP (AK a,AM a))
Proof
  strip_tac >> drule dft_packet_table_alignment >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `!a e. (a,e) IN FDOM blocks ==> _` mp_tac >>
  qpat_x_assum `AM = _` mp_tac >> qpat_x_assum `AK = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  ` (a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!e. MEM e order <=> _` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = _` mp_tac >>
  qpat_x_assum `!a e. (a,e) IN FDOM blocks ==> _` mp_tac >>
  qpat_x_assum `MEM kv _` mp_tac >>
  qpat_x_assum `FLOOKUP ms_tab (a,e) = _` mp_tac >>
  qpat_x_assum `FLOOKUP ks_tab (a,e) = _` mp_tac >>
  qpat_x_assum `MEM e order` mp_tac >>
  qpat_x_assum `AM = _` mp_tac >> qpat_x_assum `AK = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  simp[] >> irule dft_packet_flat_pair >> simp[] >>
  qexists_tac `e` >> simp[] >> metis_tac[]
QED

Theorem dft_packet_parent_pair[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
  !e cid a sf tf inc entry order res nrest kv.
    FLOOKUP acts ((e,cid)::a) = SOME (sf,tf,inc,entry,order,res,nrest) /\
    MEM kv (ZIP (AK ((e,cid)::a),AM ((e,cid)::a))) ==>
    (?sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)) /\
    MEM kv (ZIP (AK a,AM a))
Proof
  strip_tac >> drule dft_packet_block_pair >>
  disch_then (qspecl_then [`AM`,`AK`] mp_tac) >>
  qpat_assum `AM = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `AK = _` (fn th => rewrite_tac[GSYM th]) >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `AM = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qpat_assum `AK = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
    (mp_tac o cj 10) >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (fn th => mp_tac (cj 1 th) >> mp_tac (cj 5 th) >> mp_tac (cj 1 (cj 7 th))) >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `!a e rows keyrows kv. _ ==> MEM kv (ZIP (AK a,AM a))` mp_tac >>
  qpat_x_assum `AM' = _` mp_tac >> qpat_x_assum `AK' = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt (FIRST [gen_tac, disch_then strip_assume_tac]) >> gnvs[] >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _` drule >>
  disch_then (qspecl_then [`e`,`cid`,`a`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. _ ==> _` drule >>
  strip_tac >>
  conj_tac >- metis_tac[] >>
  Cases_on `FLOOKUP ms_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP es_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP ks_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> !sf tf inc entry order res nrest. _` drule >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> LIST_REL _ _ _` drule >> simp[] >> disch_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> LENGTH ms = LENGTH xs` drule >> simp[] >> disch_tac >>
  qpat_x_assum `!a e rows keyrows kv. _` irule >>
  goal_assum (drule_at Any) >> simp[] >>
  irule dft_packet_row_pair >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem dft_packet_activation_pair_root[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
  !a sf tf inc entry order res nrest kv.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    MEM kv (ZIP (AK a,AM a)) ==>
    MEM kv (ZIP (AK [],AM []))
Proof
  strip_tac >> drule dft_packet_parent_pair >>
  disch_then (qspecl_then [`AM`,`AK`] mp_tac) >>
  qpat_assum `AM = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `AK = _` (fn th => rewrite_tac[GSYM th]) >> disch_tac >>
  qpat_x_assum `AM = _` kall_tac >> qpat_x_assum `AK = _` kall_tac >>
  Induct >- simp[] >> rpt strip_tac >> PairCases_on `h` >>
  qpat_x_assum `!e cid a sf tf inc entry order res nrest kv. _` drule >>
  simp[] >> strip_tac >> metis_tac[]
QED

Theorem dft_packet_retained_pair_root:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
  !a e rows keyrows kv.
    FLOOKUP ms_tab (a,e) = SOME rows /\
    FLOOKUP ks_tab (a,e) = SOME keyrows /\
    MEM kv (ZIP (FLAT keyrows,FLAT rows)) ==>
    MEM kv (ZIP (AK [],AM []))
Proof
  strip_tac >> drule dft_packet_activation_pair_root >>
  disch_then (qspecl_then [`AM`,`AK`] mp_tac) >>
  qpat_assum `AM = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `AK = _` (fn th => rewrite_tac[GSYM th]) >> disch_tac >>
  drule dft_packet_block_pair >>
  disch_then (qspecl_then [`AM`,`AK`] mp_tac) >>
  qpat_assum `AM = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `AK = _` (fn th => rewrite_tac[GSYM th]) >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` (mp_tac o cj 1) >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `!a e rows keyrows kv. _ ==> MEM kv (ZIP (AK a,AM a))` mp_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest kv.
    _ ==> MEM kv (ZIP (AK [],AM []))` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` drule >> strip_tac >> metis_tac[]
QED

Theorem dft_packet_observed_pair[local]:
  !keys slots obs key w.
    PERM (MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs ==>
    (MEM (key,w) obs <=> MEM (key,SOME w) (ZIP (keys,slots)))
Proof
  rpt gen_tac >> strip_tac >>
  drule sortingTheory.PERM_MEM_EQ >>
  disch_then (qspec_then `(key,w)` mp_tac) >>
  simp[MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
  strip_tac >> eq_tac >> rpt strip_tac
  >- (gvs[] >> Cases_on `p_2` >> gvs[]) >>
  first_x_assum (irule o iffLR) >> qexists_tac `SOME w` >> simp[]
QED

Theorem dft_packet_root_cell_lookup[local]:
  !keys slots obs key slot.
    ALL_DISTINCT keys /\ LENGTH keys = LENGTH slots /\
    ALL_DISTINCT (MAP FST obs) /\
    PERM (MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs /\
    MEM (key,slot) (ZIP (keys,slots)) ==>
    slot = ALOOKUP obs key
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,slots)))` by simp[MAP_ZIP] >>
  `ALOOKUP (ZIP (keys,slots)) key = SOME slot` by
    metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
  drule dft_packet_observed_pair >> strip_tac >>
  Cases_on `slot`
  >- (Cases_on `ALOOKUP obs key` >> simp[] >>
      drule alistTheory.ALOOKUP_MEM >> strip_tac >>
      `MEM (key,SOME x) (ZIP (keys,slots))` by metis_tac[] >>
      metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11,
        optionTheory.NOT_NONE_SOME]) >>
  `MEM (key,x) obs` by metis_tac[] >>
  metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem dft_packet_retained_lookup:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
  LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT ks) (FLAT ms)
Proof
  strip_tac >> drule dft_packet_retained_pair_root >> disch_tac >>
  drule dft_packet_table_alignment >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!AM AK. _` (qspecl_then [`AM`,`AK`] mp_tac) >>
  qpat_assum `AM = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `AK = _` (fn th => rewrite_tac[GSYM th]) >> strip_tac >>
  qpat_x_assum `!a e rows keyrows kv. _ ==> MEM kv (ZIP (AK [],AM []))` mp_tac >>
  qpat_x_assum `!a e. (a,e) IN FDOM blocks ==> _` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (AK [])` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (MAP FST obs')` mp_tac >>
  qpat_x_assum `LENGTH (AM []) = LENGTH (AK [])` mp_tac >>
  qpat_x_assum `PERM _ obs'` mp_tac >>
  qpat_x_assum `(j,obs) = _` mp_tac >>
  qpat_x_assum `FLOOKUP ms_tab (a,e) = SOME ms` mp_tac >>
  qpat_x_assum `FLOOKUP ks_tab (a,e) = SOME ks` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  ` (a,e) IN FDOM blocks` by metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `LENGTH (FLAT ks) = LENGTH (FLAT ms)` by metis_tac[optionTheory.THE_DEF] >>
  simp[LIST_REL_EVERY_ZIP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> irule dft_packet_root_cell_lookup >>
  (metis_tac[])
QED

Theorem dft_packet_table_row_alignment[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks
Proof
  rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (mp_tac o cj 5) >>
  qpat_x_assum `FLOOKUP ms_tab (a,e) = SOME ms` mp_tac >>
  qpat_x_assum `FLOOKUP ks_tab (a,e) = SOME ks` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` drule >> strip_tac >>
  Cases_on `x8`
  >- (qpat_x_assum `case NONE of NONE => _ | SOME v => _` mp_tac >>
      simp[] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >>
  Cases_on `FLOOKUP es_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` drule >> simp[]
QED

Theorem dft_packet_retained_prefix_lookup:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
  !q. LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE q ks)) (FLAT (TAKE q ms))
Proof
  strip_tac >> drule_all dft_packet_retained_lookup >> disch_tac >>
  drule_all dft_packet_table_row_alignment >> disch_tac >>
  drule_all dft_packet_unflat_lookup >>
  metis_tac[dft_packet_flat_prefix_lookup]
QED

Theorem dft_packet_fresh_alookup[local]:
  !obs K w key. ~MEM K (MAP FST obs) ==>
    ALOOKUP (obs ++ [(K,w)]) key =
      (if key = K then SOME w else ALOOKUP obs key)
Proof
  rpt strip_tac >> rename1 `~MEM fresh (MAP FST obs)` >>
  Cases_on `key = fresh`
  >- gvs[alistTheory.ALOOKUP_APPEND, GSYM alistTheory.ALOOKUP_NONE] >>
  Cases_on `ALOOKUP obs key` >> simp[alistTheory.ALOOKUP_APPEND]
QED

Theorem dft_packet_fresh_row_lookup[local]:
  !obs K w ks ms.
    ~MEM K (MAP FST obs) /\
    LIST_REL (\key slot. slot = ALOOKUP obs key) ks ms ==>
    LIST_REL (\key slot. slot = ALOOKUP (obs ++ [(K,w)]) key) ks
      (MAP2 (\slot key. if key = K then SOME w else slot) ms ks)
Proof
  rpt gen_tac >> qid_spec_tac `ms` >> qid_spec_tac `ks` >>
  Induct >> Cases_on `ms` >> simp[] >> rpt strip_tac >>
  simp[dft_packet_fresh_alookup]
QED

Theorem dft_packet_fresh_rows_lookup[local]:
  !obs K w ks ms.
    ~MEM K (MAP FST obs) /\
    LIST_REL (LIST_REL (\key slot. slot = ALOOKUP obs key)) ks ms ==>
    LIST_REL (LIST_REL (\key slot. slot = ALOOKUP (obs ++ [(K,w)]) key)) ks
      (MAP2 (\row keys.
        MAP2 (\slot key. if key = K then SOME w else slot) row keys) ms ks)
Proof
  rpt gen_tac >> qid_spec_tac `ms` >> qid_spec_tac `ks` >>
  Induct >> Cases_on `ms` >> simp[] >> rpt strip_tac >>
  metis_tac[dft_packet_fresh_row_lookup]
QED

Theorem dft_packet_retained_fresh_lookup:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  ~MEM fresh (MAP FST obs) ==>
  !w q. LIST_REL (\key slot. slot = ALOOKUP (obs ++ [(fresh,w)]) key)
    (FLAT (TAKE q ks))
    (FLAT (TAKE q (MAP2 (\row keys.
      MAP2 (\slot key. if key = fresh then SOME w else slot) row keys) ms ks)))
Proof
  strip_tac >> drule_all dft_packet_retained_lookup >> disch_tac >>
  drule_all dft_packet_table_row_alignment >> disch_tac >>
  drule_all dft_packet_unflat_lookup >> disch_tac >> gen_tac >>
  drule_all dft_packet_fresh_rows_lookup >>
  metis_tac[dft_packet_flat_prefix_lookup]
QED

Theorem dft_packet_trace_prefix_fresh[local]:
  !visits j.
    ALL_DISTINCT (MAP FST visits) /\ j < LENGTH visits ==>
    ~MEM (FST (EL j visits)) (MAP FST (trace_gas (TAKE j visits)))
Proof
  rpt strip_tac >> drule dftGasFromListTraceNamesTheory.trace_gas_name_mem >>
  rewrite_tac[GSYM MAP_TAKE, MEM_EL] >> strip_tac >>
  gvs[LENGTH_TAKE, EL_TAKE] >>
  `EL n (MAP FST visits) = EL j (MAP FST visits)` by simp[EL_MAP, EL_TAKE] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, arithmeticTheory.LESS_TRANS,
    prim_recTheory.LESS_REFL]
QED

Theorem dft_packet_gas_fresh[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused ==>
  ~MEM (p,d,inst.inst_id) (MAP FST obs)
Proof
  rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `(j,obs) = _` mp_tac >>
  qpat_x_assum `LIST_REL dft_fn_rel _ _` mp_tac >>
  qpat_x_assum `j' < LENGTH _` mp_tac >>
  qpat_x_assum `EL j' _ = _` mp_tac >>
  qpat_x_assum `obs' = _` mp_tac >>
  qpat_x_assum `lookup_function nm C8.ctx_functions = SOME root_tf` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id)
    bb.bb_instructions)) f.fn_blocks) C8.ctx_functions` by
    metis_tac[dft_ctx_block_ids_distinct] >>
  `MEM root_tf C8.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    root_tf.fn_blocks` by
    (qpat_x_assum `EVERY _ C8.ctx_functions` mp_tac >>
     pure_rewrite_tac [EVERY_MEM] >> disch_then (qspec_then `root_tf` mp_tac) >> simp[]) >>
  `ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry))` by
    (irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >> simp[]) >>
  drule_all dft_packet_trace_prefix_fresh >> simp[]
QED

Theorem dft_packet_body_native_data[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) ==>
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  hbe <= j /\ j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,(HD ys).inst_id),fn,HD ys,be) /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bt /\
  bb_well_formed bt /\
  ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  FOLDR (dft_exec_cons (N-d) C8) OK (TAKE count ys) be = OK s
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `(j,obs) = _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _` mp_tac >>
  qpat_x_assum `FLOOKUP acts p = SOME (sf,_,_,_,_,NONE,NONE)` mp_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
  qpat_x_assum `LIST_REL dft_fn_rel _ _` mp_tac >>
  qpat_x_assum `o1_ctx_shape C8` mp_tac >>
  qpat_x_assum `lookup_function nm C8.ctx_functions = SOME root_tf` mp_tac >>
  qpat_x_assum `j' < LENGTH _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _` drule >> strip_tac >>
  qpat_x_assum `case SOME (be,hbe) of _ => _ | _ => _` mp_tac >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` drule >> strip_tac >>
  `MEM fn C8.ctx_functions` by
    (qpat_x_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
     qpat_x_assum `MEM sf C7.ctx_functions` mp_tac >>
     qpat_x_assum `fn = dft_fn sf` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  `wf_function fn` by
    (qpat_assum `o1_ctx_shape C8` mp_tac >>
     qpat_assum `MEM fn C8.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM]) >>
  `MEM bt fn.fn_blocks` by
    (qpat_assum `lookup_block bb.bb_label fn.fn_blocks = SOME bt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def]) >>
  `bb_well_formed bt` by metis_tac[venomWfTheory.wf_function_def] >>
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id)
    bb.bb_instructions)) f.fn_blocks) C8.ctx_functions` by
    metis_tac[dft_ctx_block_ids_distinct] >>
  `MEM root_tf C8.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    root_tf.fn_blocks` by
    (qpat_x_assum `EVERY _ C8.ctx_functions` mp_tac >>
     pure_rewrite_tac [EVERY_MEM] >> disch_then (qspec_then `root_tf` mp_tac) >> simp[]) >>
  `ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry))` by
    (irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem dft_packet_current_body_cursor[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) ==>
  count < LENGTH ys /\ s.vs_inst_idx = LENGTH ps + count /\
  inst = EL count ys /\ get_instruction bt s.vs_inst_idx = SOME inst /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`, `(j,obs) = _`,
     `FLOOKUP blocks (p,d) = _`, `FLOOKUP blocks (p,d) = _`,
     `case body_entry of NONE => _ | SOME v => _`,
     `get_instruction _ _ = SOME inst'`, `EL j' _ = _`, `obs' = trace_gas _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
QED

Theorem dft_packet_current_prefix_observations:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) ==>
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block p d (N-d) C8 fn
    (bt with bb_instructions := TAKE (LENGTH ps + count) bt.bb_instructions) be))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_current_body_cursor >> strip_tac >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel` kall_tac >>
  rename1 `TAKE m ys` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE m ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `m < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomWfTheory.bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `hbe < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by decide_tac >>
  `?rest. trace_blocks [] 0 N C8 root_tf root_entry =
      TAKE hbe (trace_blocks [] 0 N C8 root_tf root_entry) ++
      trace_block p d (N-d) C8 fn bt be ++ rest` by
    (qpat_assum `hbe < LENGTH _` mp_tac >>
     qpat_assum `EL hbe _ = _` mp_tac >>
     qpat_assum `lookup_block be.vs_current_bb fn.fn_blocks = SOME bt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all native_trace_blocks_continuation >> strip_tac >> gvs[] >>
     metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
  `be.vs_inst_idx + m <= LENGTH bt.bb_instructions` by simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE m (DROP be.vs_inst_idx bt.bb_instructions))` by simp[DROP_LENGTH_APPEND] >>
  `FOLDR (dft_exec_cons (N-d) C8) OK
    (TAKE m (DROP be.vs_inst_idx bt.bb_instructions)) be = OK s` by simp[DROP_LENGTH_APPEND] >>
  `hbe <= LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by decide_tac >>
  drule_all native_trace_embedded_prefix_cut >> strip_tac >>
  gvs[dftGasFromListReadingsTheory.trace_gas_append, EVERY_MEM]
QED

Theorem dft_packet_call_rooted_setup:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count ms q.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  FLOOKUP ms_tab (p,d) = SOME ms /\ inst.inst_opcode = INVOKE /\ q = EL count rho ==>
  q < LENGTH xs /\ EL q xs = inst /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  (!F kgss tail u. N <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
    FOLDR (dft_exec_cons (F-d) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
    (!callee args. setup_callee callee args (u with vs_gas_readings := s.vs_gas_readings) =
      setup_callee callee args s))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_current_prefix_observations >> strip_tac >>
  drule_all dft_packet_current_body_cursor >> strip_tac >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  rename1 `q = EL pos sched` >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`, `(j,obs) = _`,
     `FLOOKUP acts p = SOME (sf,_,_,_,_,NONE,NONE)`,
     `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> MEM sf C7.ctx_functions /\ _`,
     `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`,
     `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
       FLOOKUP blocks (a,e) = _ /\ _ ==> _`,
     `!bb bt ps xs ys rho in_state h0 be hbe count sf inc entry order.
       FLOOKUP acts p = _ /\ _ ==> _`,
     `FDOM blocks = FDOM es_tab`, `FDOM blocks = FDOM ks_tab`,
     `ALL_DISTINCT (MAP FST obs')`, `LIST_REL dft_fn_rel _ _`,
     `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),pos,OK s,F,NONE)`,
     `FLOOKUP ms_tab (p,d) = SOME ms`, `inst.inst_opcode = INVOKE`,
     `q = EL pos sched`, `pos < LENGTH ys`, `inst = EL pos ys`,
     `EVERY _ (trace_gas _)`,
     `FOLDR _ OK (TAKE pos ys) be = OK s`, `bb_well_formed bt`,
     `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o SRULE []) >>
  qpat_x_assum `(j,obs) = _` (strip_assume_tac o SRULE []) >>
  map_every (fn pat => qpat_x_assum pat (SUBST_ALL_TAC o SYM))
    [`fn = fn'`, `inst = inst'`, `s = st`, `obs = obs'`, `j = j'`] >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = _ ==> MEM sf C7.ctx_functions /\ _` drule >> strip_tac >>
  `inv_memory_observation inst.inst_opcode` by simp[inv_memory_observation_def] >>
  qpat_x_assum `!bb bt ps xs ys rho in_state h0 be hbe count sf inc entry order.
    FLOOKUP acts p = _ /\ _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` drule >>
  disch_then (strip_assume_tac o SRULE []) >>
  qpat_x_assum `FLOOKUP acts p = SOME (sf',tf,_,_,_,_,_)` mp_tac >>
  qpat_assum `FLOOKUP acts p = SOME (sf,fn,_,_,_,NONE,NONE)`
    (fn th => pure_rewrite_tac [th, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  strip_tac >>
  map_every (fn pat => qpat_x_assum pat (SUBST_ALL_TAC o SYM))
    [`sf = sf'`, `fn = tf`] >>
  `q < LENGTH xs` by
    (qpat_assum `LIST_REL _ sched ys` mp_tac >>
     qpat_assum `pos < LENGTH ys` mp_tac >>
     qpat_assum `q = EL pos sched` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `EL q xs = inst /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE pos sched))` by
    (qpat_assum `q = EL pos sched` mp_tac >>
     qpat_assum `EL (EL pos sched) xs = inst` mp_tac >>
     qpat_assum `EVERY _ (TAKE (EL pos sched) xs)` mp_tac >>
     qpat_assum `!r. r < EL pos sched /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  reverse (rpt conj_tac) >- (suspend "caller_Q") >> simp[]
QED

Resume dft_packet_call_rooted_setup[caller_Q]:
  rpt gen_tac >> strip_tac >>
  `?ess. FLOOKUP es_tab (p,d) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `FLOOKUP es_tab (p,d)` >> gvs[FLOOKUP_DEF]) >>
  `?ks. FLOOKUP ks_tab (p,d) = SOME ks` by
    (qpat_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `FLOOKUP ks_tab (p,d)` >> gvs[FLOOKUP_DEF]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!sf tf inc entry order res nrest. FLOOKUP acts p = _ ==> _` drule_all >>
  strip_tac >>
  qpat_x_assum `!F k kgss tail. _ ==> _`
    (qspecl_then [`F'`, `q`, `kgss`, `tail`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >> strip_tac >>
  drule_all dft_packet_retained_prefix_lookup >>
  disch_then (qspec_then `q` assume_tac) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (TAKE q ms)) (FLAT kgss)` by
    (qpat_assum `LIST_REL (LIST_REL _) (TAKE q ms) kgss` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule dft_packet_flat_prefix_lookup >>
     disch_then (qspec_then `LENGTH (TAKE q ms)` mp_tac) >>
     drule LIST_REL_LENGTH >> simp[]) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `ALL_DISTINCT (_ ++ _)`
       (mp_tac o REWRITE_RULE [ALL_DISTINCT_APPEND]) >> simp[NoAsms]) >>
  drule_all dft_packet_lookup_overlap >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE pos ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `pos < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomWfTheory.bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `xs = TAKE q xs ++ inst::DROP (SUC q) xs` by
    (qpat_assum `q < LENGTH xs` mp_tac >>
     qpat_assum `EL q xs = inst` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule TAKE_DROP_SUC >> simp[]) >>
  `ys = TAKE pos ys ++ inst::DROP (SUC pos) ys` by
    (qpat_assum `pos < LENGTH ys` mp_tac >>
     qpat_assum `inst = EL pos ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule TAKE_DROP_SUC >> simp[]) >>
  `MEM bb sf.fn_blocks` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  irule dftGasInvCallerExtractTheory.native_invoke_caller_observations >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK u`)) >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK s`)) >>
  goal_assum (drule_at (Pat `be.vs_inst_idx = LENGTH _`)) >>
  `LENGTH (TAKE q xs) = q /\ LENGTH (TAKE pos ys) = pos` by
    (qpat_assum `q < LENGTH xs` mp_tac >>
     qpat_assum `pos < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_assum `LENGTH (TAKE q xs) = q` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `LENGTH (TAKE pos ys) = pos` (fn th => pure_rewrite_tac[th]) >>
  goal_assum (drule_at (Pat `trace_gas _ = ZIP _`)) >>
  qexistsl [`bt`, `fn`] >>
  qrefinel [`_`, `bb.bb_label`, `_`, `_`, `_`] >>
  goal_assum (drule_at (Pat `EVERY _ (trace_gas _)`)) >>
  qexistsl [`DROP (SUC pos) ys`, `DROP (SUC q) xs`, `inst`] >>
  qpat_assum `xs = TAKE q xs ++ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `ys = TAKE pos ys ++ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `LENGTH (FLAT (TAKE q ks)) = LENGTH (FLAT kgss)` by
    (qpat_assum `LIST_REL (\key slot. _) (FLAT (TAKE q ks)) _` mp_tac >>
     qpat_assum `LIST_REL (\slot w. _) (FLAT (TAKE q ms)) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[LIST_REL_LENGTH]) >>
  simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise dft_packet_call_rooted_setup

Theorem dft_packet_body_native_slice:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count fuel post t.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  SUC count < LENGTH ys /\ inst = EL count ys /\
  s.vs_inst_idx = LENGTH ps + count /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel C8 inst s = OK post /\
  t = post with vs_inst_idx := SUC s.vs_inst_idx /\
  SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,(EL (SUC count) ys).inst_id),fn,EL (SUC count) ys,t) ==>
  TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    TAKE hbe (trace_blocks [] 0 N C8 root_tf root_entry) ++
    trace_block p d (N-d) C8 fn
      (bt with bb_instructions := TAKE (LENGTH ps + SUC count) bt.bb_instructions) be
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel` kall_tac >>
  rename1 `SUC m < LENGTH ys` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (SUC m) ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `SUC m < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomWfTheory.bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `step_inst (N-d) C8 inst s = OK post` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `FOLDR (dft_exec_cons (N-d) C8) OK (TAKE (SUC m) ys) be = OK t` by
    (`TAKE (SUC m) ys = TAKE m ys ++ [inst]` by
       simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE m ys)` by
       gvs[EVERY_APPEND] >>
     asm_rewrite_tac[FOLDR_APPEND] >>
     drule dftRunRelTheory.dft_exec_prefix_continue >>
     disch_then assume_tac >> simp[] >>
     qpat_assum `inst = _` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     qpat_assum `~is_terminator inst.inst_opcode` mp_tac >>
     qpat_assum `step_inst (N-d) C8 inst s = OK post` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[dftIndexedExecTheory.dft_exec_cons_def]) >>
  `hbe < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by decide_tac >>
  `?rest. trace_blocks [] 0 N C8 root_tf root_entry =
      TAKE hbe (trace_blocks [] 0 N C8 root_tf root_entry) ++
      trace_block p d (N-d) C8 fn bt be ++ rest` by
    (qpat_assum `hbe < LENGTH _` mp_tac >>
     qpat_assum `EL hbe _ = _` mp_tac >>
     qpat_assum `lookup_block be.vs_current_bb fn.fn_blocks = SOME bt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all native_trace_blocks_continuation >> strip_tac >> gvs[] >>
     metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
  `t.vs_inst_idx = be.vs_inst_idx + SUC m` by simp[] >>
  `get_instruction bt t.vs_inst_idx = SOME (EL (SUC m) ys)` by
    simp[venomInstTheory.get_instruction_def, EL_APPEND2] >>
  `be.vs_inst_idx + SUC m <= LENGTH bt.bb_instructions` by simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE (SUC m) (DROP be.vs_inst_idx bt.bb_instructions))` by simp[DROP_LENGTH_APPEND] >>
  `FOLDR (dft_exec_cons (N-d) C8) OK
    (TAKE (SUC m) (DROP be.vs_inst_idx bt.bb_instructions)) be = OK t` by simp[DROP_LENGTH_APPEND] >>
  `hbe <= LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by decide_tac >>
  drule_all native_trace_embedded_prefix_cut >> simp[]
QED

Theorem dft_packet_body_target_observations:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count fuel post t.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  SUC count < LENGTH ys /\ inst = EL count ys /\
  s.vs_inst_idx = LENGTH ps + count /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel C8 inst s = OK post /\
  t = post with vs_inst_idx := SUC s.vs_inst_idx /\
  SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,(EL (SUC count) ys).inst_id),fn,EL (SUC count) ys,t) ==>
  EVERY (\kw. MEM kw (trace_gas (TAKE (SUC j)
      (trace_blocks [] 0 N C8 root_tf root_entry))))
    (trace_gas (trace_block p d (N-d) C8 fn
      (bt with bb_instructions := TAKE (LENGTH ps + SUC count) bt.bb_instructions) be))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_body_native_slice >> disch_then SUBST1_TAC >>
  simp[dftGasFromListReadingsTheory.trace_gas_append, EVERY_MEM]
QED

Theorem dft_packet_fresh_pair_none[local]:
  !keys slots obs key0 v.
    PERM (MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs /\
    ~MEM key0 (MAP FST obs) /\ MEM (key0,v) (ZIP (keys,slots)) ==>
    v = NONE
Proof
  rpt strip_tac >> Cases_on `v` >> simp[] >>
  `MEM (key0,x) obs` by
    (drule sortingTheory.PERM_MEM_EQ >>
     disch_then (qspec_then `(key0,x)` (fn th => rewrite_tac[GSYM th])) >>
     simp[MEM_MAP, MEM_FILTER] >> qexists_tac `(key0,SOME x)` >> simp[]) >>
  gvs[MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem dft_packet_current_gas_key:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    AM AK bb bt ps xs ys rho in_state h0 be hbe count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  inst.inst_opcode = GAS ==>
  ~MEM (p,d,inst.inst_id) (MAP FST obs) /\
  ?n. n < LENGTH (AK []) /\ EL n (AK []) = (p,d,inst.inst_id) /\
    EL n (AM []) = NONE
Proof
  rpt gen_tac >> strip_tac >> drule dft_packet_gas_fresh >> disch_tac >>
  conj_tac >- simp[] >>
  drule dft_packet_retained_pair_root >>
  disch_then (qspecl_then [`AM`,`AK`] mp_tac) >>
  qpat_assum `AM = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `AK = _` (fn th => rewrite_tac[GSYM th]) >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `AM = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qpat_assum `AK = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (fn th => mp_tac (cj 1 th) >> mp_tac (cj 5 th) >> mp_tac (cj 1 (cj 7 th))) >>
  qpat_x_assum `!a e rows keyrows kv. _ ==> MEM kv (ZIP (AK [],AM []))` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `PERM _ obs'` mp_tac >>
  qpat_x_assum `LENGTH (AM' []) = LENGTH (AK' [])` mp_tac >>
  qpat_x_assum `AM' = AM` mp_tac >> qpat_x_assum `AK' = AK` mp_tac >>
  qpat_x_assum `(j,obs) = _` mp_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,_,_,_,SOME _,_,_,_,_)` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
  qpat_x_assum `case body_entry of NONE => _ | SOME v => _` mp_tac >>
  qpat_x_assum `FLOOKUP acts p = _` mp_tac >>
  qpat_x_assum `inst.inst_opcode = GAS` mp_tac >>
  qpat_x_assum `~MEM _ (MAP FST obs)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (fn th => map_every (SUBST_ALL_TAC o SYM)
      (CONJUNCTS (PURE_REWRITE_RULE [joint_config_11] th))) >>
  qpat_x_assum `(j,obs) = _`
    (fn th => map_every (SUBST_ALL_TAC o SYM)
      (CONJUNCTS (PURE_REWRITE_RULE [pairTheory.PAIR_EQ] th))) >>
  qpat_x_assum `AM' = AM` SUBST_ALL_TAC >>
  qpat_x_assum `AK' = AK` SUBST_ALL_TAC >>
  qpat_x_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,_,_,_,SOME _,_,_,_,_)`
    (fn th => qpat_x_assum `FLOOKUP blocks (p,d) = _`
      (fn other => map_every (SUBST_ALL_TAC o SYM)
        (CONJUNCTS (PURE_REWRITE_RULE
          [th,optionTheory.SOME_11,pairTheory.PAIR_EQ] other))) >>
      assume_tac th) >>
  qpat_x_assum `case SOME _ of NONE => _ | SOME v => _`
    (strip_assume_tac o SRULE []) >>
  qpat_x_assum `inst = EL _ _` SUBST_ALL_TAC >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` drule >> strip_tac >>
  `EL count' rho' < LENGTH xs /\
   (EL count' ys).inst_id = (EL (EL count' rho') xs).inst_id /\
   from_block [EL (EL count' rho') xs] (EL count' ys)` by
    (qpat_x_assum `LIST_REL _ rho' ys` mp_tac >>
     rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
     first_x_assum (qspec_then `count'` mp_tac) >> simp[]) >>
  `(EL (EL count' rho') xs).inst_opcode = GAS` by
    (qpat_x_assum `from_block _ _` mp_tac >>
     qpat_x_assum `(EL count' ys).inst_opcode = GAS` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rw[dftStructuralTheory.from_block_def] >> gvs[] >>
     drule dftShapeTheory.flip_operands_special_opcode >> simp[]) >>
  Cases_on `FLOOKUP ms_tab (p,d)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP es_tab (p,d)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP ks_tab (p,d)` >- gvs[FLOOKUP_DEF] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> !sf tf inc entry order res nrest. _` drule >>
  simp[] >> disch_then assume_tac >>
  qpat_x_assum `!q. q < LENGTH ys ==> _`
    (qspec_then `EL count' rho'` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> LIST_REL _ _ _` drule >> simp[] >> disch_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> LENGTH ms = LENGTH xs` drule >> simp[] >> disch_tac >>
  `MEM ((p,d,(EL count' ys).inst_id),ALOOKUP obs (p,d,(EL count' ys).inst_id))
    (ZIP (FLAT x'',FLAT x))` by
    (irule dft_packet_row_pair >> goal_assum (drule_at Any) >>
     qexists_tac `EL count' rho'` >> simp[]) >>
  `MEM ((p,d,(EL count' ys).inst_id),ALOOKUP obs (p,d,(EL count' ys).inst_id))
    (ZIP (AK [],AM []))` by
    (qpat_x_assum `!a e rows keyrows kv. _` irule >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `MEM _ (ZIP (AK [],AM []))` mp_tac >>
  qpat_x_assum `~MEM _ (MAP FST obs)` mp_tac >>
  qpat_x_assum `PERM _ obs` mp_tac >>
  qpat_x_assum `LENGTH (AM []) = LENGTH (AK [])` mp_tac >>
  qpat_x_assum `(EL count' ys).inst_id = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  drule_all dft_packet_fresh_pair_none >> disch_tac >>
  gvs[MEM_ZIP] >> metis_tac[]
QED

Theorem dft_packet_current_gas_copies_none:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused ==>
  !a e rows keyrows v.
    FLOOKUP ms_tab (a,e) = SOME rows /\
    FLOOKUP ks_tab (a,e) = SOME keyrows /\
    MEM ((p,d,inst.inst_id),v) (ZIP (FLAT keyrows,FLAT rows)) ==>
    v = NONE
Proof
  strip_tac >> drule dft_packet_gas_fresh >> disch_tac >>
  drule dft_packet_retained_pair_root >>
  disch_then (qspecl_then
    [`\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))`,
     `\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))`] mp_tac) >>
  simp[] >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `PERM _ obs'` mp_tac >>
  qpat_x_assum `AM = _` mp_tac >> qpat_x_assum `AK = _` mp_tac >>
  qpat_x_assum `(j,obs) = _` mp_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `~MEM _ (MAP FST obs)` mp_tac >>
  qpat_x_assum `!a e rows keyrows kv. _ ==> MEM kv _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  metis_tac[dft_packet_fresh_pair_none]
QED

(* A key is generated by a GAS row, or copied from a recorded child.
   The finite activation domain makes repeated strict-child descent finite. *)
Theorem dft_packet_retained_key_step[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  MEM (b,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order)) ==>
  (?bb bt ps xs ys rho hin h0 be hbe count front closed brest q.
    FLOOKUP blocks (b,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ (EL q xs).inst_opcode = GAS /\ (EL q xs).inst_id = cid) \/
  (?a' sf' tf' inc' entry' order' res' rest'.
    LENGTH a' = SUC (LENGTH a) /\
    FLOOKUP acts a' = SOME (sf',tf',inc',entry',order',res',rest') /\
    MEM (b,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a',f)))) order')))
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` (mp_tac o cj 7) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `AK = _` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = _` mp_tac >>
  qpat_x_assum `MEM (b,e,cid) _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  qpat_x_assum `MEM (b,e,cid) _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_FLAT,MEM_MAP]) >>
  rename1 `MEM f order` >>
  `(a,f) IN FDOM blocks` by metis_tac[] >>
  `?bv. FLOOKUP blocks (a,f) = SOME bv` by
    metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
  PairCases_on `bv` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _` (drule_then strip_assume_tac) >>
  Cases_on `bv8`
  >- (qpat_x_assum `case NONE of NONE => _ | SOME v => _` mp_tac >>
      simp[] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >>
  `?ms ess ks. FLOOKUP ms_tab (a,f) = SOME ms /\
    FLOOKUP es_tab (a,f) = SOME ess /\ FLOOKUP ks_tab (a,f) = SOME ks` by
    metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  `?q. q < LENGTH ks /\ MEM (b,e,cid) (EL q ks)` by
    metis_tac[MEM_FLAT,MEM_EL] >>
  qpat_x_assum `!q. q < LENGTH _ ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL q bv3).inst_opcode = GAS`
  >- (gvs[] >> disj1_tac >> goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `(EL q bv3).inst_opcode = INVOKE`
  >- (Cases_on `FLOOKUP calls (a,f,(EL q bv3).inst_id)` >- gvs[] >>
      PairCases_on `x` >>
      qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
        FLOOKUP calls (a,e,cid) = _ ==> _` (drule_then strip_assume_tac) >>
      disj2_tac >> goal_assum (drule_at Any) >> simp[] >> gvs[]) >>
  gvs[]
QED

Theorem dft_packet_retained_key_origin:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  MEM (b,e,cid) (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order)) ==>
  ?bb bt ps xs ys rho hin h0 be hbe count front closed brest q.
    FLOOKUP blocks (b,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ (EL q xs).inst_opcode = GAS /\ (EL q xs).inst_id = cid
Proof
  strip_tac >>
  qabbrev_tac `B = SUC (MAX_SET (IMAGE LENGTH (FDOM acts)))` >>
  `!a v. FLOOKUP acts a = SOME v ==> LENGTH a < B` by
    (qx_gen_tac `path` >> qx_gen_tac `v` >> strip_tac >>
     `LENGTH path <= MAX_SET (IMAGE LENGTH (FDOM acts))` by
       (irule in_max_set >> simp[] >>
        metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
     simp[Abbr `B`]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`MEM (b,e,cid) _`, `FLOOKUP acts a = _`] >>
  map_every qid_spec_tac [`nrest`,`res`,`order`,`entry`,`inc`,`tf`,`sf`,`a`] >>
  gen_tac >> measureInduct_on `B - LENGTH a` >> rpt strip_tac >>
  drule_all dft_packet_retained_key_step >> strip_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  `LENGTH a' < B` by metis_tac[] >> decide_tac
QED

Theorem dft_packet_empty_body_key_fresh:
  !order bb bt ps xs ys rho hin h0 st.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,NONE,0,OK st,F,NONE) ==>
  !cid. ~MEM (p,d,cid)
    (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab ([],f)))) order))
Proof
  rpt strip_tac >> drule_all dft_packet_retained_key_origin >>
  strip_tac >> gvs[]
QED

Theorem dft_packet_selected_body[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e bb bt ps xs ys rho hin h0 be hbe
    count front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
  ?sp. bb.bb_instructions = ps ++ xs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK sp /\
    (!F. FOLDR (dft_exec_cons (F-e) C8) OK
      (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be) /\
    LENGTH (THE (FLOOKUP ms_tab (a,e))) = LENGTH xs
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (mp_tac o cj 1) >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `case SOME (be,hbe) of _ => _ | _ => _` mp_tac >>
  simp[] >> strip_tac >>
  `?ms. FLOOKUP ms_tab (a,e) = SOME ms` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `?ks. FLOOKUP ks_tab (a,e) = SOME ks` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (drule_then strip_assume_tac) >> gvs[] >>
  gen_tac >>
  qpat_x_assum `FOLDR _ _ _ _ = OK be` mp_tac >>
  `EVERY (\i. is_pseudo i.inst_opcode)
    (DROP (phi_prefix_length (ps ++ ys)) ps)` by simp[EVERY_DROP] >>
  metis_tac[dft_packet_pseudo_fuel]
QED

Theorem dft_packet_selected_input[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 body count front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
  MEM e order /\
  (e = SUC inc ==> hin = entry) /\
  (e <> SUC inc ==>
    ?pb pt pps pxs pys prho pin ph pbe pc pu.
      FLOOKUP blocks (a,e-1) =
        SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu)) /\
  (body = NONE ==> ~closed) /\
  (e <> LAST order ==> closed)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = SOME _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _` (drule_then strip_assume_tac) >>
  strip_tac >> gvs[]
QED

Theorem dft_packet_selected_closed[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 bentry count post rest fuel.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,bentry,count,OK post,T,SOME rest) /\ N <= fuel ==>
  ?be hbe sp. bentry = SOME (be,hbe) /\
    bb.bb_instructions = ps ++ xs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK sp /\
    FOLDR (dft_exec_cons (fuel-e) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    (!vs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
        (FLAT (THE (FLOOKUP ms_tab (a,e)))) vs ==>
      ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
         (be with vs_gas_readings := vs ++ tail))) ==>
       residual_result tail (OK post)
         (FOLDR (dft_exec_cons (fuel-e) C7) OK xs
           (be with vs_gas_readings := vs ++ tail))))
Proof
  rpt gen_tac >> strip_tac >>
  `bentry <> NONE` by
    (drule_all dft_packet_selected_input >> simp[]) >>
  Cases_on `bentry` >> gvs[] >> PairCases_on `x` >>
  drule_all dft_packet_selected_body >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    _ ==> _` (mp_tac o cj 4) >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  qpat_x_assum `N <= fuel` mp_tac >>
  qpat_x_assum `eval_phis hin (ps ++ ys) = OK _` mp_tac >>
  qpat_x_assum `!F. FOLDR _ _ _ _ = OK _` mp_tac >>
  qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) ys` mp_tac >>
  qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs` mp_tac >>
  qpat_x_assum `EVERY (\i. is_pseudo i.inst_opcode) ps` mp_tac >>
  qpat_x_assum `bb.bb_instructions = ps ++ xs` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `?ms. FLOOKUP ms_tab (a,e) = SOME ms` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `?ks. FLOOKUP ks_tab (a,e) = SOME ks` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    _ ==> _` (drule_all_then mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`x0`,`x1`,`sp`] >> simp[] >>
  metis_tac[]
QED

Theorem dft_packet_closed_row_residual:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front rest ms fuel gs tail.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,T,SOME rest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\
  ((?post. front = OK post) \/ (?ir out. front = IntRet ir out)) /\
  N <= fuel /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs /\
  (?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
    (be with vs_gas_readings := gs ++ tail))) ==>
  residual_result tail front (FOLDR (dft_exec_cons (fuel-e) C7) OK xs
    (be with vs_gas_readings := gs ++ tail))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    _ ==> _` (mp_tac o cj 4) >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP ms_tab (a,e) = SOME _` mp_tac >>
  qpat_x_assum `N <= fuel` mp_tac >>
  qpat_x_assum `LIST_REL _ (FLAT ms) gs` mp_tac >>
  qpat_x_assum `terminates _` mp_tac >>
  qpat_x_assum `front = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `?ks. FLOOKUP ks_tab (a,e) = SOME ks` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    _ ==> _` (drule_all_then mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem dft_packet_closed_row_key_success:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front rest ms ks fuel gs tail v.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,T,SOME rest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= fuel /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs /\
  (FOLDR (dft_exec_cons (fuel-e) C7) OK xs
     (be with vs_gas_readings := gs ++ tail) = OK v \/
   ?ir. FOLDR (dft_exec_cons (fuel-e) C7) OK xs
     (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
  MAP FST (dftGasFromListTraceDefs$trace_gas
    (dftGasFromListTraceDefs$trace_block a e (fuel-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
      (be with vs_gas_readings := gs ++ tail))) = FLAT ks
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    _ ==> _` (mp_tac o cj 4) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (mp_tac o cj 5) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`FDOM blocks = FDOM es_tab`, `FLOOKUP acts a = SOME _`,
     `FLOOKUP blocks (a,e) = SOME _`, `FLOOKUP ms_tab (a,e) = SOME _`,
     `FLOOKUP ks_tab (a,e) = SOME _`, `N <= fuel`,
     `LIST_REL _ (FLAT ms) gs`, `FOLDR _ _ _ _ = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` (drule_all_then assume_tac) >>
  `LENGTH (FLAT ms) = LENGTH (FLAT ks)` by
    (`MAP LENGTH ms = MAP LENGTH ks` by
       metis_tac[MAP_EQ_LIST_REL, LIST_REL_LENGTH] >>
     simp[LENGTH_FLAT]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    _ ==> _` (drule_all_then mp_tac) >>
  simp[] >> strip_tac >>
  `dftGasFromListTraceDefs$trace_gas
    (dftGasFromListTraceDefs$trace_block a e (fuel-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
      (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)` by metis_tac[] >>
  simp[] >> irule (cj 1 MAP_ZIP) >> metis_tac[LIST_REL_LENGTH]
QED

Theorem dft_packet_selected_order_entries:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused fuel a sf tf inc entry order res nrest
    ds e later bb bt ps xs ys rho hin h0 be hbe count front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  N <= fuel /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  order = ds ++ e::later /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
  ?entries rows slotss sp.
    entries = MAP (\f. case THE (FLOOKUP blocks (a,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf) ds ++ [hin] /\
    rows = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds /\
    slotss = MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds /\
    HD entries = entry /\ LAST entries = hin /\
    LENGTH entries = SUC (LENGTH rows) /\ LENGTH slotss = LENGTH rows /\
    (!r. r < LENGTH rows ==>
      ?br er pr xr yr sr ber.
        EL r rows = (br,er,DROP (phi_prefix_length br.bb_instructions) br.bb_instructions) /\
        br.bb_instructions = pr ++ xr /\
        EVERY (\i. is_pseudo i.inst_opcode) pr /\
        EVERY (\i. ~is_pseudo i.inst_opcode) xr /\
        EVERY (\i. ~is_pseudo i.inst_opcode) yr /\
        eval_phis (EL r entries) (pr ++ yr) = OK sr /\
        FOLDR (dft_exec_cons (fuel-er) C8) OK
          (DROP (phi_prefix_length (pr ++ yr)) pr)
          (sr with vs_inst_idx := phi_prefix_length (pr ++ yr)) = OK ber /\
        (!vs rest.
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL r slotss) vs ==>
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xr
             (ber with vs_gas_readings := vs ++ rest))) ==>
           residual_result rest (OK (EL (SUC r) entries))
             (FOLDR (dft_exec_cons (fuel-er) C7) OK xr
               (ber with vs_gas_readings := vs ++ rest))))) /\
    bb.bb_instructions = ps ++ xs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK sp /\
    FOLDR (dft_exec_cons (fuel-e) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    LENGTH (THE (FLOOKUP ms_tab (a,e))) = LENGTH xs
Proof
  rpt gen_tac >> strip_tac >>
  `order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
   (!f. MEM f order <=> (a,f) IN FDOM blocks)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
     qpat_x_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `!r. r <= LENGTH ds ==>
    EL r (ds ++ [e]) = inc + SUC r /\ MEM (inc + SUC r) order` by
    (rpt strip_tac >>
     `r < LENGTH order` by gvs[] >>
     `EL r order = inc + SUC r` by
       (qpat_assum `order = GENLIST _ _` (fn th => once_rewrite_tac[th]) >>
        simp[EL_GENLIST]) >>
     `EL r (ds ++ [e]) = EL r order` by
       (gvs[EL_APPEND_EQN] >> Cases_on `r < LENGTH ds` >> gvs[]) >>
     metis_tac[EL_MEM]) >>
  qabbrev_tac `gin = (\f. case THE (FLOOKUP blocks (a,f)) of
    (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf)` >>
  `gin e = hin` by simp[Abbr `gin`] >>
  `!r. r <= LENGTH ds ==>
    EL r (MAP gin ds ++ [hin]) = gin (inc + SUC r)` by
    (rpt strip_tac >>
     `MAP gin ds ++ [hin] = MAP gin (ds ++ [e])` by simp[] >>
     qpat_x_assum `MAP gin ds ++ [hin] = _`
       (fn th => pure_once_rewrite_tac[th]) >>
     simp[EL_MAP]) >>
  `!f. MEM f order ==>
    ?bf btf psf xsf ysf rhof inf hf bef cf rf closedf restf.
      FLOOKUP blocks (a,f) = SOME (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) /\
      gin f = inf` by
    (rpt strip_tac >>
     `?v. FLOOKUP blocks (a,f) = SOME v` by
       metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
     PairCases_on `v` >> simp[Abbr `gin`] >> metis_tac[]) >>
  `gin (SUC inc) = entry` by
    (`MEM (SUC inc) order` by
       (qpat_x_assum `!r. r <= LENGTH ds ==> _ /\ _`
          (qspec_then `0` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
     qpat_x_assum `!f. MEM f order ==> _` drule >> strip_tac >>
     drule_all dft_packet_selected_input >> simp[]) >>
  drule_all dft_packet_selected_body >> strip_tac >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!r. r <= LENGTH ds ==> EL r _ = gin _`
        (qspec_then `0` mp_tac) >> gvs[arithmeticTheory.ADD1]) >>
  rpt strip_tac >>
  `SUC r <= LENGTH ds` by simp[] >>
  `MEM (inc + SUC (SUC r)) order` by metis_tac[] >>
  qpat_x_assum `!f. MEM f order ==> _` drule >> strip_tac >>
  drule_all dft_packet_selected_input >> simp[] >> strip_tac >>
  `inc + SUC (SUC r) - 1 = inc + SUC r` by simp[] >>
  qpat_x_assum `FLOOKUP blocks (a,_ - 1) = _` mp_tac >>
  simp[] >> strip_tac >>
  drule_all dft_packet_selected_closed >> strip_tac >>
  `gin (inc + SUC r) = pin` by simp[Abbr `gin`] >>
  `EL r ds = inc + SUC r` by
    (qpat_x_assum `!r. r <= LENGTH ds ==> _ /\ _`
       (qspec_then `r` mp_tac) >> simp[EL_APPEND_EQN]) >>
  qexistsl_tac [`pb`,`inc + SUC r`,`pps`,`pxs`,`pys`,`sp'`,`be'`] >>
  simp[EL_MAP] >>
  qpat_x_assum `!vs tail. LIST_REL _ _ _ ==> _` mp_tac >> simp[]
QED

Theorem dft_packet_refined_selected_order[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused fuel W a sf tf inc entry order res nrest
    ds e later bb bt ps xs ys rho hin h0 be hbe count front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FDOM W = FDOM ms_tab /\
  (!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP W key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new) /\
  N <= fuel /\ FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  order = ds ++ e::later /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
  ?entries rows slotss sp.
    entries = MAP (\f. case THE (FLOOKUP blocks (a,f)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf) ds ++ [hin] /\
    rows = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds /\
    slotss = MAP (\f. FLAT (THE (FLOOKUP W (a,f)))) ds /\
    HD entries = entry /\ LAST entries = hin /\
    LENGTH entries = SUC (LENGTH rows) /\ LENGTH slotss = LENGTH rows /\
    (!r. r < LENGTH rows ==>
      ?br er pr xr yr sr ber.
        EL r rows = (br,er,DROP (phi_prefix_length br.bb_instructions) br.bb_instructions) /\
        br.bb_instructions = pr ++ xr /\
        EVERY (\i. is_pseudo i.inst_opcode) pr /\
        EVERY (\i. ~is_pseudo i.inst_opcode) xr /\
        EVERY (\i. ~is_pseudo i.inst_opcode) yr /\
        eval_phis (EL r entries) (pr ++ yr) = OK sr /\
        FOLDR (dft_exec_cons (fuel-er) C8) OK
          (DROP (phi_prefix_length (pr ++ yr)) pr)
          (sr with vs_inst_idx := phi_prefix_length (pr ++ yr)) = OK ber /\
        (!vs rest.
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL r slotss) vs ==>
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xr
             (ber with vs_gas_readings := vs ++ rest))) ==>
           residual_result rest (OK (EL (SUC r) entries))
             (FOLDR (dft_exec_cons (fuel-er) C7) OK xr
               (ber with vs_gas_readings := vs ++ rest))))) /\
    bb.bb_instructions = ps ++ xs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK sp /\
    FOLDR (dft_exec_cons (fuel-e) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    LENGTH (THE (FLOOKUP W (a,e))) = LENGTH xs
Proof
  rpt gen_tac >> strip_tac >> rename1 `FDOM work = FDOM ms_tab` >>
  drule_all dft_packet_selected_order_entries >> strip_tac >>
  `!key. key IN FDOM blocks ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new))
      (THE (FLOOKUP ms_tab key)) (THE (FLOOKUP work key))` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     qpat_x_assum `FDOM work = FDOM ms_tab` mp_tac >>
     qpat_x_assum `!key old new. _ ==> LIST_REL _ old new` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `?old. FLOOKUP ms_tab key = SOME old` by gvs[FLOOKUP_DEF] >>
     `?new. FLOOKUP work key = SOME new` by gvs[FLOOKUP_DEF] >>
     simp[] >> metis_tac[]) >>
  `!f. MEM f (ds ++ [e]) ==> (a,f) IN FDOM blocks` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
     qpat_x_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` mp_tac >>
     qpat_x_assum `order = ds ++ e::later` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >> gvs[MEM_APPEND] >> metis_tac[]) >>
  `LENGTH (THE (FLOOKUP work (a,e))) = LENGTH xs` by
    metis_tac[LIST_REL_LENGTH, MEM_APPEND, MEM] >>
  gvs[] >> rpt strip_tac >>
  qpat_x_assum `!r. r < LENGTH ds ==> _` (drule_then strip_assume_tac) >>
  qexistsl_tac [`br`,`er`,`pr`,`xr`,`yr`,`sr`,`ber`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  conj_tac >- metis_tac[] >> simp[EL_MAP] >>
  irule dft_packet_refined_flat_compatible >>
  qexists_tac `THE (FLOOKUP work (a,EL r ds))` >>
  reverse conj_tac >- gvs[EL_MAP] >>
  first_x_assum irule >> first_x_assum irule >> simp[EL_MEM]
QED

Theorem dft_packet_suspended_prefix_bound:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q call_h b0 done_at_call
    child_entry bb bt ps xs ys rho in_state h0 be hbe count k.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
  done_at_call = TAKE count rho /\
  (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) ==>
  q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
  ~MEM q (TAKE count rho) /\ k <= q
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==> _` mp_tac >>
  qpat_x_assum `FLOOKUP calls (a,e,cid) = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  qpat_x_assum `done_at_call = TAKE _ _` mp_tac >>
  qpat_x_assum `!r. r < k /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret. _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `~(q < k)` by metis_tac[] >> simp[]
QED

Theorem dft_packet_call_done_contained:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q call_h b0 done child_entry ret
    bb bt ps xs ys rho hin h0 be hbe count front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,child_entry,ret) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
  !r. MEM r done ==> MEM r (TAKE count rho)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==> _` mp_tac >>
  qpat_x_assum `!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
      q h b0 done child_entry cid e a. _` mp_tac >>
  qpat_x_assum `FLOOKUP calls (a,e,cid) = SOME _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret. _`
    (drule_then strip_assume_tac) >> gvs[] >>
  rename1 `MEM r (TAKE (b0.vs_inst_idx - LENGTH ps) rr)` >>
  rename1 `MEM r (TAKE cc rr)` >>
  Cases_on `ret`
  >- (gvs[MEM_GENLIST] >> rename1 `(e,_)::a = DROP k p` >>
      `k < LENGTH p` by
        (Cases_on `k = LENGTH p` >> gvs[] >> decide_tac) >>
      `DROP k p = EL k p :: DROP (SUC k) p` by simp[DROP_CONS_EL] >>
      qpat_x_assum `!k. k < LENGTH p ==> _` (qspec_then `k` mp_tac) >> simp[] >>
      strip_tac >> gvs[] >>
      `LAST order = e` by metis_tac[pairTheory.PAIR_EQ] >>
      qpat_x_assum `FLOOKUP blocks (_,LAST order) = _` mp_tac >>
      qpat_x_assum `FLOOKUP blocks (_,e) = _` mp_tac >>
      qpat_x_assum `LAST order = e` mp_tac >>
      qpat_x_assum `TAKE _ _ = TAKE _ _` mp_tac >>
      qpat_x_assum `MEM r _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[])
  >> PairCases_on `x` >> gvs[] >>
  `b0.vs_inst_idx - LENGTH ps < cc` by
    (spose_not_then assume_tac >>
     `TAKE cc rr = TAKE cc (TAKE (b0.vs_inst_idx - LENGTH ps) rr)` by
       (sym_tac >> irule TAKE_TAKE_T >> decide_tac) >>
     metis_tac[MEM_TAKE]) >>
  `TAKE (b0.vs_inst_idx - LENGTH ps) rr =
    TAKE (b0.vs_inst_idx - LENGTH ps) (TAKE cc rr)` by (sym_tac >> irule TAKE_TAKE_T >> decide_tac) >>
  metis_tac[MEM_TAKE]
QED

Theorem dft_packet_refined_call_prefix[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused fuel W a e cid q call_h b0 done child_entry ret
    bb bt ps xs ys rho hin h0 be hbe count front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done,child_entry,ret) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FDOM W = FDOM ms_tab /\
  (!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP W key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new) /\
  N <= fuel /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r done) ==>
  q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
  (?nm ops args ctf.
    decode_invoke (EL q xs) = SOME (nm,ops) /\
    lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry) /\
  (!kgss rest caller.
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE q (THE (FLOOKUP W (a,e)))) kgss /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ rest) = OK caller ==>
    caller.vs_gas_readings = rest /\
    (!op. MEM op (EL q xs).inst_operands ==> eval_operand op caller = eval_operand op b0) /\
    (!callee argv. setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0))
Proof
  rpt gen_tac >> strip_tac >> rename1 `FDOM work = FDOM ms_tab` >>
  rename1 `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rr,hin,h0,SOME (be,hbe),cc,front,closed,brest)` >>
  `!r. MEM r done ==> MEM r (TAKE cc rr)` by metis_tac[dft_packet_call_done_contained] >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==> _`
    (drule_then strip_assume_tac) >>
  `?ms ess ks new. FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    FLOOKUP work (a,e) = SOME new` by
    (qpat_x_assum `FDOM work = _` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
     qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = _ /\ FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ ==> _`
    drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qpat_x_assum `!F kgss tail u. _` mp_tac >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` mp_tac >>
  qpat_x_assum `!r. MEM r done ==> _` mp_tac >>
  qpat_x_assum `!r. r < q /\ _ ==> _` mp_tac >>
  qpat_x_assum `EVERY _ (TAKE q xs)` mp_tac >>
  qpat_x_assum `N <= fuel` mp_tac >>
  qpat_x_assum `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP work key = SOME new ==> _` mp_tac >>
  qpat_x_assum `FLOOKUP ms_tab (a,e) = _` mp_tac >>
  qpat_x_assum `FLOOKUP work (a,e) = _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rr,hin,h0,SOME (be,hbe),cc,front,closed,brest)` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = _` mp_tac >>
  qpat_x_assum `q < LENGTH _` mp_tac >>
  qpat_x_assum `_ = EL q _` mp_tac >>
  qpat_x_assum `_.inst_id = cid` mp_tac >>
  qpat_x_assum `_.inst_opcode = INVOKE` mp_tac >>
  qpat_x_assum `decode_invoke _ = SOME _` mp_tac >>
  qpat_x_assum `lookup_function _ C8.ctx_functions = _` mp_tac >>
  qpat_x_assum `eval_operands _ b0 = _` mp_tac >>
  qpat_x_assum `setup_callee _ _ b0 = SOME child_entry` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >> gvs[] >>
  rpt gen_tac >> strip_tac >>
  `LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) ms new` by metis_tac[] >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss` by
    (irule dft_packet_refined_take_compatible >> qexists_tac `new` >> simp[]) >>
  reverse conj_tac
  >- (qpat_x_assum `!F kgss tail u. N <= F /\ _ ==> _` (drule_all_then strip_assume_tac) >> simp[]) >>
  qpat_x_assum `!F k kgss tail. _`
    (qspecl_then [`fuel`,`q`,`kgss`,`rest`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem dft_packet_cut_row_alignment:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused W a e bb bt ps xs ys rho hin h0
    be hbe count front closed brest q z cuts levels Mcut fuel gs tail events u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FDOM W = FDOM ms_tab /\
  (!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP W key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
      else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) =
            SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
            MEM r done_at_call)) /\
      EL i levels =
        (sfi,
         MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
           [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP W (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP W (ai,ei))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) ==>
  ?Mbefore gpre kgss v.
    Mcut = Mbefore ++ FLAT (TAKE q (THE (FLOOKUP W (a,e)))) /\
    gs = gpre ++ FLAT kgss /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE q (THE (FLOOKUP W (a,e)))) kgss /\
    v = (hin with vs_gas_readings := FLAT kgss ++ tail) /\
    (case eval_phis v bb.bb_instructions of
      OK sp => FOLDR (dft_exec_cons (fuel-e) C7) OK z
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    | other => other) = OK u /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `FDOM work = FDOM ms_tab` >>
  `!i. ?entries rows slotss bb ps xs ys sp be depth q z ms sf.
    i < LENGTH cuts ==>
    (!ai ds ei qi zi. EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?tf inc ent order res nrest bt rho hin h0 hbe count front closed brest later.
        FLOOKUP acts ai = SOME (sf,tf,inc,ent,order,res,nrest) /\
        FLOOKUP blocks (ai,ei) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
        HD entries = ent /\ LAST entries = hin /\ order = ds ++ ei::later /\
        depth = ei /\ q = qi /\ z = zi /\
        rows = MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds /\
        slotss = MAP (\f. FLAT (THE (FLOOKUP work (ai,f)))) ds /\
        ms = THE (FLOOKUP work (ai,ei))) /\
    EL i levels = (sf,rows ++ [(bb,depth,z)],
      if SUC i = LENGTH cuts then NONE else SOME (EL q xs)) /\
    LENGTH entries = SUC (LENGTH rows) /\ LENGTH slotss = LENGTH rows /\
    (!r. r < LENGTH rows ==>
      ?br er pr xr yr sr ber.
        EL r rows = (br,er,DROP (phi_prefix_length br.bb_instructions) br.bb_instructions) /\
        br.bb_instructions = pr ++ xr /\ EVERY (\x. is_pseudo x.inst_opcode) pr /\
        EVERY (\x. ~is_pseudo x.inst_opcode) xr /\ EVERY (\x. ~is_pseudo x.inst_opcode) yr /\
        eval_phis (EL r entries) (pr ++ yr) = OK sr /\
        FOLDR (dft_exec_cons (fuel-er) C8) OK (DROP (phi_prefix_length (pr ++ yr)) pr)
          (sr with vs_inst_idx := phi_prefix_length (pr ++ yr)) = OK ber /\
        (!vs rest. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL r slotss) vs ==>
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xr
            (ber with vs_gas_readings := vs ++ rest))) ==>
           residual_result rest (OK (EL (SUC r) entries))
            (FOLDR (dft_exec_cons (fuel-er) C7) OK xr
              (ber with vs_gas_readings := vs ++ rest))))) /\
    bb.bb_instructions = ps ++ xs /\ EVERY (\x. is_pseudo x.inst_opcode) ps /\
    EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
    eval_phis (LAST entries) (ps ++ ys) = OK sp /\
    FOLDR (dft_exec_cons (fuel-depth) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    q < LENGTH xs /\ LENGTH ms = LENGTH xs /\
    (SUC i < LENGTH cuts ==>
      EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
      ?b0 nm ops args ctf child_entry csf ctf' cinc corder cres crest.
        FLOOKUP acts (EL (SUC i) (MAP (\(ai,ds,ei,qi,zi). ai) cuts)) =
          SOME (csf,ctf',cinc,child_entry,corder,cres,crest) /\
        (EL q xs).inst_opcode = INVOKE /\ decode_invoke (EL q xs) = SOME (nm,ops) /\
        lookup_function nm C8.ctx_functions = SOME ctf /\
        eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
        (!kgss rest caller.
          LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
          FOLDR (dft_exec_cons (fuel-depth) C7) OK (TAKE q xs)
            (be with vs_gas_readings := FLAT kgss ++ rest) = OK caller ==>
          caller.vs_gas_readings = rest /\
          (!op. MEM op (EL q xs).inst_operands ==> eval_operand op caller = eval_operand op b0) /\
          (!callee argv. setup_callee callee argv (caller with vs_gas_readings := b0.vs_gas_readings) =
            setup_callee callee argv b0)))` by
    (gen_tac >> Cases_on `i < LENGTH cuts`
     >- (qabbrev_tac `ci = EL i cuts` >> PairCases_on `ci` >>
         `EL i cuts = (ci0,ci1,ci2,ci3,ci4)` by metis_tac[Abbr `ci`] >>
         qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> _`
           (drule_all_then strip_assume_tac) >>
         `?bei0 bei1. bei = SOME (bei0,bei1)` by
           (Cases_on `SUC i = LENGTH cuts`
            >- (qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >>
                asm_rewrite_tac[] >> disch_then strip_assume_tac >>
                gvs[] >>
                qpat_x_assum `FLOOKUP blocks (ci0,ci2) = _` mp_tac >>
                qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
                POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
            qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >>
            simp[] >> strip_tac >>
            qhdtm_x_assum `dft_focus_packet_rel`
              (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
            qpat_x_assum `!a e cid q h b0 done child_entry ret.
              FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==> _`
              (drule_then strip_assume_tac) >>
            qpat_x_assum `FLOOKUP blocks (ci0,ci2) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti)` mp_tac >>
            qpat_x_assum `FLOOKUP blocks (ci0,ci2) = _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
         qpat_x_assum `bei = SOME _` SUBST_ALL_TAC >>
         drule_all dft_packet_refined_selected_order >> strip_tac >>
         qexistsl_tac [`entries`,`rows`,`slotss`,`bbi`,`psi`,`xsi`,`ysi`,`sp`,`bei0`,
           `ci2`,`ci3`,`ci4`,`THE (FLOOKUP work (ci0,ci2))`,`sfi`] >>
         simp[] >>
         Cases_on `SUC i = LENGTH cuts`
         >- (qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >>
             asm_rewrite_tac[] >> disch_then strip_assume_tac >>
             `bbi = bb /\ psi = ps /\ xsi = xs` by
               (qpat_x_assum `FLOOKUP blocks (ci0,ci2) = _` mp_tac >>
                qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
                qpat_x_assum `ci0 = a` mp_tac >> qpat_x_assum `ci2 = e` mp_tac >>
                POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
             gvs[]) >>
         qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >>
         asm_rewrite_tac[] >> disch_then strip_assume_tac >>
         drule_all dft_packet_refined_call_prefix >> strip_tac >>
         `?csf ctf' cinc corder cres crest.
           FLOOKUP acts ((ci2,cid)::ci0) =
             SOME (csf,ctf',cinc,child_entry,corder,cres,crest)` by
           (qhdtm_x_assum `dft_focus_packet_rel`
              (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
            qpat_x_assum `!a e cid q h b0 done child_entry ret.
              FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==> _`
              (drule_then strip_assume_tac) >> (simp[])) >>
         simp[] >> metis_tac[]) >> simp[]) >>
  qpat_x_assum `!i. ?entries rows slotss bb ps xs ys sp be depth q z ms sf. _`
    (qx_choosel_then [`entries`,`rows`,`slotss`,`bbs`,`pss`,`xss`,`yss`,`sps`,
      `bes`,`depths`,`qs`,`zs`,`mss`,`sfs`] assume_tac o SIMP_RULE bool_ss [SKOLEM_THM]) >>
  `LENGTH cuts = SUC (LENGTH a)` by
    (qpat_x_assum `MAP _ cuts = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[LENGTH_MAP,LENGTH_REVERSE,LENGTH_GENLIST]) >>
  `cuts <> []` by (Cases_on `cuts` >> gvs[]) >>
  `0 < LENGTH cuts` by simp[] >>
  `HD (MAP (\(ai,ds,ei,qi,zi). ai) cuts) = []` by
    (simp[HD_REVERSE,GENLIST_LAST,GENLIST_EQ_NIL]) >>
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?tf inc res nrest bt rho h0 hbe count front closed brest later.
      FLOOKUP acts ai = SOME (sfs i,tf,inc,HD (entries i),ds ++ ei::later,res,nrest) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbs i,bt,pss i,xss i,yss i,rho,LAST (entries i),h0,
          SOME (bes i,hbe),count,front,closed,brest) /\
      depths i = ei /\ qs i = qi /\ zs i = zi /\
      rows i = MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
        DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
          (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds /\
      slotss i = MAP (\f. FLAT (THE (FLOOKUP work (ai,f)))) ds /\
      mss i = THE (FLOOKUP work (ai,ei))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH cuts ==> _`
       (drule_then (mp_tac o CONJUNCT1)) >> simp[]) >>
  `HD (entries 0) = root_entry` by
    (qabbrev_tac `ci = EL 0 cuts` >> PairCases_on `ci` >>
     `EL 0 cuts = (ci0,ci1,ci2,ci3,ci4)` by metis_tac[Abbr `ci`] >>
     `ci0 = []` by
       (qpat_x_assum `HD (MAP _ cuts) = []` mp_tac >>
        qpat_x_assum `EL 0 cuts = _` mp_tac >>
        qpat_x_assum `cuts <> []` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts` >> simp[]) >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?tf inc res nrest. _`
       (drule_all_then strip_assume_tac) >>
     qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `FLOOKUP acts ci0 = _` mp_tac >>
     qpat_x_assum `FLOOKUP acts [] = _` mp_tac >>
     qpat_x_assum `ci0 = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `!i. SUC i < LENGTH cuts ==>
    ?tf inc order res nrest.
      FLOOKUP acts (EL (SUC i) (MAP (\(ai,ds,ei,qi,zi). ai) cuts)) =
        SOME (sfs (SUC i),tf,inc,HD (entries (SUC i)),order,res,nrest)` by
    (gen_tac >> strip_tac >>
     qabbrev_tac `ci = EL (SUC i) cuts` >> PairCases_on `ci` >>
     `EL (SUC i) cuts = (ci0,ci1,ci2,ci3,ci4)` by metis_tac[Abbr `ci`] >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?tf inc res nrest. _`
       (drule_all_then strip_assume_tac) >>
     simp[EL_MAP] >> metis_tac[]) >>
  `bbs (LENGTH cuts - 1) = bb /\ xss (LENGTH cuts - 1) = xs /\
   bes (LENGTH cuts - 1) = be /\ LAST (entries (LENGTH cuts - 1)) = hin /\
   depths (LENGTH cuts - 1) = e /\ qs (LENGTH cuts - 1) = q /\
   zs (LENGTH cuts - 1) = z /\ mss (LENGTH cuts - 1) = THE (FLOOKUP work (a,e))` by
    (`LENGTH cuts - 1 < LENGTH cuts /\ SUC (LENGTH cuts - 1) = LENGTH cuts` by simp[] >>
     qabbrev_tac `ci = EL (LENGTH cuts - 1) cuts` >> PairCases_on `ci` >>
     `EL (LENGTH cuts - 1) cuts = (ci0,ci1,ci2,ci3,ci4)` by metis_tac[Abbr `ci`] >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
       bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
       FLOOKUP acts ai = _ /\ FLOOKUP blocks (ai,ei) = _ /\ orderi = ds ++ ei::later /\ _`
       (drule_all_then strip_assume_tac) >>
     qpat_x_assum `if SUC (LENGTH cuts - 1) = LENGTH cuts then _ else _` mp_tac >>
     qpat_x_assum `SUC (LENGTH cuts - 1) = LENGTH cuts` (fn th => rewrite_tac[th]) >>
     disch_then strip_assume_tac >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?tf inc res nrest. _`
       (drule_all_then strip_assume_tac) >>
     qpat_x_assum `FLOOKUP blocks (ci0,ci2) = SOME (bbs _,_)` mp_tac >>
     qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
     qpat_x_assum `ci0 = a` mp_tac >> qpat_x_assum `ci2 = e` mp_tac >>
     qpat_x_assum `ci3 = q` mp_tac >> qpat_x_assum `ci4 = z` mp_tac >>
     qpat_x_assum `depths (LENGTH cuts - 1) = _` mp_tac >>
     qpat_x_assum `qs (LENGTH cuts - 1) = _` mp_tac >>
     qpat_x_assum `zs (LENGTH cuts - 1) = _` mp_tac >>
     qpat_x_assum `mss (LENGTH cuts - 1) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qabbrev_tac `segments = (\i. FLAT (slotss i) ++ FLAT (TAKE (qs i) (mss i)))` >>
  `Mcut = FLAT (MAP segments (COUNT_LIST (LENGTH cuts)))` by
    (qpat_x_assum `Mcut = FLAT (MAP _ cuts)` SUBST1_TAC >>
     AP_TERM_TAC >> irule LIST_EQ >> simp[MAP_COUNT_LIST,LENGTH_COUNT_LIST] >>
     qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH cuts` by simp[] >>
     qabbrev_tac `ci = EL i cuts` >> PairCases_on `ci` >>
     `EL i cuts = (ci0,ci1,ci2,ci3,ci4)` by metis_tac[Abbr `ci`] >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?tf inc res nrest. _`
       (drule_all_then strip_assume_tac) >>
     simp[EL_MAP,EL_GENLIST,Abbr `segments`]) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?Mbefore gpre kgss v.
    Mbefore = FLAT (MAP segments (COUNT_LIST (LENGTH cuts - 1))) ++ FLAT (slotss (LENGTH cuts - 1)) /\
    Mcut = Mbefore ++ FLAT (TAKE (qs (LENGTH cuts - 1)) (mss (LENGTH cuts - 1))) /\
    gs = gpre ++ FLAT kgss /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE (qs (LENGTH cuts - 1)) (mss (LENGTH cuts - 1))) kgss /\
    v = (LAST (entries (LENGTH cuts - 1)) with vs_gas_readings := FLAT kgss ++ tail) /\
    SND (row_eval fuel C7 (sfs (LENGTH cuts - 1)).fn_name
      (bbs (LENGTH cuts - 1),depths (LENGTH cuts - 1),zs (LENGTH cuts - 1)) v) = OK u /\
    FOLDR (dft_exec_cons (fuel-depths (LENGTH cuts - 1)) C7) OK
      (TAKE (qs (LENGTH cuts - 1)) (xss (LENGTH cuts - 1)))
      (bes (LENGTH cuts - 1) with vs_gas_readings := FLAT kgss ++ tail) = OK u` by
    (irule (dft_packet_rooted_row_alignment |> Q.INST_TYPE
       [`:'b` |-> `:ir_function`, `:'c` |-> `:num`,
        `:'d` |-> `:exec_result option`, `:'e` |-> `:bytes32 list option`,
        `:'f` |-> `:basic_block`, `:'g` |-> `:num list`,
        `:'h` |-> `:num`, `:'i` |-> `:num`, `:'j` |-> `:num`,
        `:'k` |-> `:exec_result`, `:'l` |-> `:bool`, `:'m` |-> `:bytes32 list option`]) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     conj_tac >- (qpat_assum `row_eval = _` (fn th => rewrite_tac[th]) >>
       POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     reverse conj_tac >- (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`C8`,`work`,`acts`,`blocks`,`call_setup C7`,`events`,`levels`,
       `plan_eval fuel C7`,`pss`,`root_entry`,`rooted_eval fuel C7`,`rows`,`sps`,`yss`] >>
     conj_tac >- (qpat_assum `call_setup = _` (fn th => rewrite_tac[th]) >>
       POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     conj_tac >- (qpat_assum `plan_eval = _` (fn th => rewrite_tac[th]) >>
       POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     conj_tac >- (qpat_assum `rooted_eval = _` (fn th => rewrite_tac[th]) >>
       POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!i ai ds ei qi zi. _ ==> ?tf inc res nrest. _`
          (drule_all_then mp_tac) >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
     ntac 13 (conj_tac >- (first_assum ACCEPT_TAC)) >>
     conj_tac >- simp[Abbr `segments`] >>
     strip_tac >>
     qpat_x_assum `SUC i < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     (
        `child_entry = HD (entries (SUC i))` by
          (qpat_assum `!i. SUC i < LENGTH cuts ==> _` (drule_then strip_assume_tac) >>
           qpat_x_assum `FLOOKUP acts _ = SOME (csf,_)` mp_tac >>
           qpat_x_assum `FLOOKUP acts _ = SOME (sfs (SUC i),_)` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
        qexistsl_tac [`b0`,`nm'`,`ops`,`args`,`ctf`] >>
        qpat_x_assum `child_entry = _` (fn th => rewrite_tac[GSYM th]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`Mbefore`,`gpre`,`kgss`,`v`] >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`Mcut = Mbefore ++ _`, `gs = gpre ++ _`,
     `LIST_REL _ Mbefore gpre`, `LIST_REL (LIST_REL _) _ kgss`,
     `v = _`, `SND (row_eval _ _ _ _ _) = OK u`,
     `FOLDR _ OK (TAKE (qs _) _) _ = OK u`,
     `bbs (LENGTH cuts - 1) = bb`, `xss (LENGTH cuts - 1) = xs`,
     `bes (LENGTH cuts - 1) = be`, `LAST (entries (LENGTH cuts - 1)) = hin`,
     `depths (LENGTH cuts - 1) = e`, `qs (LENGTH cuts - 1) = q`,
     `zs (LENGTH cuts - 1) = z`, `mss (LENGTH cuts - 1) = _`,
     `row_eval = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `eval_phis vin instructions` >>
  Cases_on `eval_phis vin instructions` >> gvs[]
QED

Theorem dft_packet_cut_row_trace:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused W a e bb bt ps xs ys rho hin h0
    be hbe count front closed brest q z cuts levels Mcut fuel gs tail events u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FDOM W = FDOM ms_tab /\
  (!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP W key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
      else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) =
            SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
            MEM r done_at_call)) /\
      EL i levels =
        (sfi,
         MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
           [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP W (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP W (ai,ei))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) ==>
  ?Mbefore gpre kgss v.
    Mcut = Mbefore ++ FLAT (TAKE q (THE (FLOOKUP W (a,e)))) /\
    gs = gpre ++ FLAT kgss /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE q (THE (FLOOKUP W (a,e)))) kgss /\
    v = (hin with vs_gas_readings := FLAT kgss ++ tail) /\
    (case eval_phis v bb.bb_instructions of
      OK sp => FOLDR (dft_exec_cons (fuel-e) C7) OK z
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    | other => other) = OK u /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_block a e (fuel-e) C7
        (FST (THE (FLOOKUP acts a)))
        (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
        (be with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (TAKE q (THE (FLOOKUP ks_tab (a,e)))),FLAT kgss)
Proof
  rpt gen_tac >> strip_tac >> rename1 `FDOM work = FDOM ms_tab` >>
  drule_all dft_packet_cut_row_alignment >> strip_tac >>
  qexistsl_tac [`Mbefore`,`gpre`,`kgss`,`v`] >>
  ntac 7 (conj_tac >- (first_assum ACCEPT_TAC)) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?ms ess ks new. FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    FLOOKUP work (a,e) = SOME new` by
    (qpat_x_assum `FDOM work = _` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
     qpat_x_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _`
      (mp_then Any strip_assume_tac inv)) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`!F k kgss tail. _`,
     `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP work key = SOME new ==> _`,
     `FLOOKUP acts a = _`, `FLOOKUP ms_tab (a,e) = _`,
     `FLOOKUP ks_tab (a,e) = _`, `FLOOKUP work (a,e) = _`,
     `N <= fuel`, `q < LENGTH xs`, `EVERY _ (TAKE q xs)`,
     `!r. r < q /\ _ ==> _`,
     `LIST_REL (LIST_REL _) (TAKE q (THE (FLOOKUP work (a,e)))) kgss`,
     `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs) _ = OK u`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >> gvs[] >>
  `LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) ms new` by metis_tac[] >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss` by
    (irule dft_packet_refined_take_compatible >> qexists_tac `new` >> simp[]) >>
  qpat_x_assum `!F k kgss tail. _` (qspecl_then [`fuel`,`q`,`kgss`,`tail`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem dft_packet_closed_activation_return:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME result,SOME rest) ==>
  a <> [] /\ ?ir child_out. result = IntRet ir child_out
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` mp_tac >>
  qpat_x_assum `FLOOKUP acts [] = _` mp_tac >>
  qpat_x_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME result,SOME rest)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  Cases_on `a` >- gvs[] >> simp[] >>
  qpat_x_assum `FLOOKUP acts [] = _` kall_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _`
    (drule_then strip_assume_tac) >>
  rename1 `FLOOKUP acts (pair::parent) = _` >> PairCases_on `pair` >>
  qpat_x_assum `!e cid parent. _`
    (qspecl_then [`pair0`,`pair1`,`parent`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. _`
    (drule_then strip_assume_tac) >>
  gvs[] >> Cases_on `ret` >> gvs[] >> PairCases_on `x` >> gvs[]
QED

Theorem dft_packet_completed_call[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e bb bt ps xs ys rho hin h0 be hbe
    count front closed brest q.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
  ?call_h b0 done centry ir cout post.
    FLOOKUP calls (a,e,(EL q xs).inst_id) =
      SOME(q,call_h,b0,done,centry,SOME(ir,cout,post))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> !q. _` (drule_then mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED

Theorem dft_packet_row_prefix_readings[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks F k kgss tail u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
  FLOOKUP ks_tab (a,e) = SOME ks /\ N <= F /\ k <= LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
  (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss /\
  FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
  u.vs_gas_readings = tail
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
  rename1 `N <= fuel` >>
  qpat_x_assum `!F k kgss tail. _` (qspecl_then [`fuel`,`k`,`kgss`,`tail`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem dft_packet_call_prefix_agreement:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q call_h b0 done centry ret
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms F kgss tail u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME(q,call_h,b0,done,centry,ret) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ N <= F /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
  FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
  (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
  (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
    setup_callee callee args b0)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done child_entry ret bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = _ /\ FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ ==> _`
    (drule_all_then mp_tac) >>
  simp[]
QED

Theorem dft_packet_returned_call_alignment[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e cid q call_h b0 done centry ir cout post u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP calls (a,e,cid) = SOME(q,call_h,b0,done,centry,SOME(ir,cout,post)) /\
  (!bb bt ps xs ys rho hin h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) = SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) ==>
    (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
    (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee args b0)) ==>
  ?csf ctf corder crest c nm ops args.
    FLOOKUP acts ((e,cid)::a) = SOME(csf,ctf,e,centry,corder,SOME(IntRet ir cout),SOME crest) /\
    decode_invoke c = SOME(nm,ops) /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    lookup_function nm C7.ctx_functions = SOME csf /\
    eval_operands ops u = SOME args /\
    setup_callee csf args u = SOME(centry with vs_gas_readings := u.vs_gas_readings) /\
    (!bb bt ps xs ys rho hin h0 be hbe count front closed brest.
      FLOOKUP blocks (a,e) = SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) ==>
      c = EL q xs)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` mp_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
  qpat_x_assum `LIST_REL dft_fn_rel _ _` mp_tac >>
  qpat_x_assum `o1_ctx_shape C7` mp_tac >> qpat_x_assum `o1_ctx_shape C8` mp_tac >>
  qpat_x_assum `FLOOKUP calls (a,e,cid) = _` mp_tac >>
  qpat_x_assum `!bb bt ps xs ys rho hin h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) = SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `FLOOKUP acts a = _` kall_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `child_rest` >- gvs[] >>
  drule_all dft_packet_callee_alignment >> strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C7.ctx_functions) /\
   ALL_DISTINCT (MAP (\f. f.fn_name) C8.ctx_functions)` by
    fs[o1_ctx_shape_def,venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,venomInstTheory.ctx_fn_names_def] >>
  `lookup_function nm C7.ctx_functions = SOME csf` by
    (gvs[lookup_function_member_iff,dft_fn_rel_def]) >>
  gvs[]
QED

Theorem dft_packet_invoke_row[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks q call
    csf ctf centry corder cres crest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
  FLOOKUP calls (a,e,(EL q xs).inst_id) = SOME call /\
  FLOOKUP acts ((e,(EL q xs).inst_id)::a) = SOME(csf,ctf,e,centry,corder,cres,crest) ==>
  (?ess. FLOOKUP es_tab (a,e) = SOME ess) /\ LENGTH ms = LENGTH xs /\
  EL q ms = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (((e,(EL q xs).inst_id)::a),f)))) corder) /\
  EL q ks = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (((e,(EL q xs).inst_id)::a),f)))) corder)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `AM = _` mp_tac >> qpat_x_assum `AK = _` mp_tac >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`FLOOKUP acts a = _`, `FLOOKUP blocks (a,e) = _`,
     `FLOOKUP ms_tab (a,e) = _`, `FLOOKUP ks_tab (a,e) = _`,
     `q < LENGTH xs`, `(EL q xs).inst_opcode = INVOKE`,
     `FLOOKUP calls (a,e,(EL q xs).inst_id) = _`,
     `FLOOKUP acts ((e,(EL q xs).inst_id)::a) = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks. _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem dft_packet_closed_trace_keys[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order r8 rest F gs tail ir v.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME(sf,tf,inc,entry,order,SOME r8,SOME rest) /\
  N <= F /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) order)) gs /\
  run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v ==>
  MAP FST (trace_gas (trace_blocks a inc (F-inc) C7 sf
    (entry with vs_gas_readings := gs ++ tail))) =
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order)
Proof
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME(sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _`
    (drule_then mp_tac) >>
  qpat_x_assum `AM = _` mp_tac >> qpat_x_assum `AK = _` mp_tac >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`FLOOKUP acts a = _`, `N <= fuel`, `LIST_REL _ _ gs`,
     `run_blocks _ _ _ _ = IntRet ir v`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!gs tail. _` (qspecl_then [`gs`,`tail`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!v. _ \/ _ ==> _` (qspec_then `v` mp_tac) >>
  simp[] >> strip_tac >>
  drule LIST_REL_LENGTH >> simp[MAP_ZIP]
QED

Theorem dft_packet_call_from_child_prefix[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks F q kgss tail u k.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= F /\ q < k /\ k <= LENGTH ms /\ q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
  MEM q (TAKE count rho) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss /\
  FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
  (!csf ctf centry corder cr crest cgs ctail.
    FLOOKUP acts ((e,(EL q xs).inst_id)::a) =
      SOME(csf,ctf,e,centry,corder,SOME cr,SOME crest) /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (((e,(EL q xs).inst_id)::a),f)))) corder)) cgs ==>
    ?extra. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (((e,(EL q xs).inst_id)::a),f)))) corder) =
      MAP FST (trace_gas (trace_blocks ((e,(EL q xs).inst_id)::a) e (F-e) C7 csf
        (centry with vs_gas_readings := cgs ++ ctail))) ++ extra) ==>
  (?extra. EL q ks = MAP FST (trace_gas
    (trace_step a e (F-e) C7 sf (EL q xs) u)) ++ extra) /\
  (!v. step_inst (F-e) C7 (EL q xs) u = OK v ==>
    EL q ks = MAP FST (trace_gas (trace_step a e (F-e) C7 sf (EL q xs) u)))
Proof
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  drule_all dft_packet_completed_call >> strip_tac >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
    (TAKE q ms) (TAKE q kgss)` by
    (drule_then (qspec_then `q` mp_tac) LIST_REL_TAKE >>
     simp[TAKE_TAKE]) >>
  `FLAT kgss ++ tail = FLAT (TAKE q kgss) ++ (FLAT (DROP q kgss) ++ tail)` by
    metis_tac[TAKE_DROP,FLAT_APPEND,APPEND_ASSOC] >>
  `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT (TAKE q kgss) ++ (FLAT (DROP q kgss) ++ tail)) = OK u` by
    metis_tac[] >>
  drule_all dft_packet_call_prefix_agreement >> strip_tac >>
  drule dft_packet_returned_call_alignment >> disch_then drule >>
  disch_then (qspec_then `u` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> gvs[])) >> strip_tac >>
  gvs[] >>
  drule_all dft_packet_invoke_row >> strip_tac >>
  `q <= LENGTH xs` by simp[] >>
  `u.vs_gas_readings = FLAT (DROP q kgss) ++ tail` by
    (irule dft_packet_row_prefix_readings >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = _` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at Any) >>
     qrefinel [`_`,`_`,`TAKE q kgss`,`q`,`_`,`fuel`] >>
     simp[] >> metis_tac[]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) (EL q kgss)` by
    (gvs[LIST_REL_EL_EQN, EL_TAKE]) >>
  `q < LENGTH kgss` by gvs[LIST_REL_EL_EQN] >>
  `FLAT (DROP q kgss) = EL q kgss ++ FLAT (DROP (SUC q) kgss)` by
    (simp[DROP_CONS_EL]) >>
  conj_tac
  >- (qpat_x_assum `!cgs ctail. _`
        (qspecl_then [`EL q kgss`,`FLAT (DROP (SUC q) kgss) ++ tail`] mp_tac) >>
      impl_tac >- metis_tac[] >>
      drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >>
      simp[APPEND_ASSOC]) >>
  rpt strip_tac >>
  `?cir cv. run_blocks (fuel-e) C7 csf
    (centry with vs_gas_readings := u.vs_gas_readings) = IntRet cir cv` by
    (qpat_x_assum `step_inst _ _ _ _ = OK v` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_def,AllCaseEqs()] >>
     metis_tac[]) >>
  drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >>
  disch_then (fn th => rewrite_tac [th]) >>
  qpat_assum `EL q ks = _` SUBST1_TAC >> sym_tac >>
  asm_rewrite_tac [GSYM APPEND_ASSOC] >>
  irule dft_packet_closed_trace_keys >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts ((e,_)::a) = _` (irule_at Any) >>
  qexistsl [`cv`,`cir`] >> fs[APPEND_ASSOC]
  >> (gvs[])
QED

Theorem dft_packet_call_supplier_from_child:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks F q kgss tail u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= F /\ q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
  MEM q (TAKE count rho) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms kgss /\
  FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
  (!csf ctf centry corder cr crest cgs ctail.
    FLOOKUP acts ((e,(EL q xs).inst_id)::a) =
      SOME(csf,ctf,e,centry,corder,SOME cr,SOME crest) /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (((e,(EL q xs).inst_id)::a),f)))) corder)) cgs ==>
    ?extra. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (((e,(EL q xs).inst_id)::a),f)))) corder) =
      MAP FST (trace_gas (trace_blocks ((e,(EL q xs).inst_id)::a) e (F-e) C7 csf
        (centry with vs_gas_readings := cgs ++ ctail))) ++ extra) ==>
  (?extra. EL q ks = MAP FST (trace_gas
    (trace_step a e (F-e) C7 sf (EL q xs) u)) ++ extra) /\
  (!v. step_inst (F-e) C7 (EL q xs) u = OK v ==>
    EL q ks = MAP FST (trace_gas (trace_step a e (F-e) C7 sf (EL q xs) u)))
Proof
  rpt gen_tac >> strip_tac >>
  irule dft_packet_call_from_child_prefix >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP ms_tab (a,e) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP ks_tab (a,e) = _` (irule_at Any) >>
  qexistsl [`tail`,`kgss`,`LENGTH ms`] >> simp[] >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem dft_packet_key_refines[local]:
  !rows keys needle w.
    LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keys /\
    (!v. MEM (needle,v) (ZIP (FLAT keys,FLAT rows)) ==> v = NONE) ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) rows
      (MAP2 (\ss kk. MAP2 (\slot key. if key = needle then SOME w else slot) ss kk)
        rows keys)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH rows = LENGTH keys /\
   !i. i < LENGTH rows ==> LENGTH (EL i rows) = LENGTH (EL i keys)` by
    gvs[LIST_REL_EL_EQN] >>
  simp[Once LIST_REL_EL_EQN, EL_MAP2] >>
  qx_gen_tac `i` >> strip_tac >>
  `i < LENGTH keys /\ LENGTH (EL i rows) = LENGTH (EL i keys)` by metis_tac[] >>
  simp[LIST_REL_EL_EQN] >>
  qx_gen_tac `j` >> strip_tac >>
  simp[EL_MAP2] >> Cases_on `EL j (EL i keys) = needle` >> simp[] >>
  disj1_tac >> first_x_assum irule >> irule dft_packet_row_pair >>
  goal_assum (drule_at Any) >> qexists_tac `i` >> simp[MEM_ZIP] >>
  qexists_tac `j` >> simp[]
QED

Theorem dft_packet_keymap_refines[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused work w.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  work = FMAP_MAP2 (\(ae,rows).
    MAP2 (\ss kk. MAP2 (\slot key.
      if key = (p,d,inst.inst_id) then SOME w else slot) ss kk)
      rows (THE (FLOOKUP ks_tab ae))) ms_tab ==>
  FDOM work = FDOM ms_tab /\
  (!ae old new. FLOOKUP ms_tab ae = SOME old /\ FLOOKUP work ae = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- simp[FMAP_MAP2_THM] >>
  rpt gen_tac >> PairCases_on `ae` >> strip_tac >>
  `?keys. FLOOKUP ks_tab (ae0,ae1) = SOME keys` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
     qpat_x_assum `FLOOKUP ms_tab (ae0,ae1) = SOME old` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  drule_all dft_packet_table_row_alignment >> strip_tac >>
  drule dft_packet_current_gas_copies_none >> disch_tac >>
  `new = MAP2 (\ss kk. MAP2 (\slot key.
    if key = (p,d,inst.inst_id) then SOME w else slot) ss kk) old keys` by
    gvs[FLOOKUP_FMAP_MAP2] >>
  asm_rewrite_tac[] >> irule dft_packet_key_refines >>
  simp[] >> metis_tac[]
QED

Theorem dft_packet_activation_rows[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
  !e. MEM e order ==>
    ?rows keys. FLOOKUP ms_tab (a,e) = SOME rows /\
      FLOOKUP ks_tab (a,e) = SOME keys /\
      LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keys
Proof
  strip_tac >> rpt strip_tac >>
  `(a,e) IN FDOM ms_tab /\ (a,e) IN FDOM ks_tab` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` (mp_tac o cj 7) >>
     qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
     qpat_x_assum `MEM e order` mp_tac >>
     qpat_x_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `?rows keys. FLOOKUP ms_tab (a,e) = SOME rows /\
    FLOOKUP ks_tab (a,e) = SOME keys` by
    metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME] >>
  drule_all dft_packet_table_row_alignment >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem dft_packet_keymap_activation[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  work = FMAP_MAP2 (\(ae,rows).
    MAP2 (\ss kk. MAP2 H ss kk) rows (THE (FLOOKUP ks_tab ae))) ms_tab /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
  FLAT (MAP (\e. FLAT (THE (FLOOKUP work (a,e)))) order) =
    MAP2 H (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) order))
      (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order))
Proof
  strip_tac >> irule dft_key_map_order_flat >>
  goal_assum (drule_at Any) >> metis_tac[dft_packet_activation_rows]
QED

Theorem dft_packet_keymap_root[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  work = FMAP_MAP2 (\(ae,rows).
    MAP2 (\ss kk. MAP2 H ss kk) rows (THE (FLOOKUP ks_tab ae))) ms_tab /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  newAM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP work (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) ==>
  newAM [] = MAP2 H (AM []) (AK [])
Proof
  strip_tac >>
  `?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     goal_assum (drule_at Any)) >>
  drule_all dft_packet_keymap_activation >> simp[]
QED

Theorem dft_packet_keymap_gas_conservation[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    work w tail AM AK newAM bb bt ps xs ys rho in_state h0 be hbe count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  work = FMAP_MAP2 (\(ae,rows).
    MAP2 (\ss kk. MAP2 (\slot key.
      if key = (p,d,inst.inst_id) then SOME w else slot) ss kk)
      rows (THE (FLOOKUP ks_tab ae))) ms_tab /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  newAM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP work (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  inst.inst_opcode = GAS /\ s.vs_gas_readings = w::tail ==>
  LENGTH (newAM []) = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME (newAM [])) ++ tail)
    (MAP THE (FILTER IS_SOME raw_slots) ++ s.vs_gas_readings) /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],newAM []))))
    (obs ++ [((p,d,inst.inst_id),w)])
Proof
  rpt gen_tac >> strip_tac >> drule_all dft_packet_keymap_root >> disch_tac >>
  drule_all dft_packet_current_gas_key >> strip_tac >>
  `raw_slots = AM [] /\ LENGTH (AM []) = LENGTH sites /\
    LENGTH (AM []) = LENGTH (AK []) /\ ALL_DISTINCT (AK []) /\
    PERM (MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     map_every (fn pat => qpat_x_assum pat mp_tac)
       [`AM' = _`, `AK' = _`, `raw_slots = _`, `sites = _`,
        `LENGTH (AM' []) = LENGTH (AE [])`,
        `LENGTH (AM' []) = LENGTH (AK' [])`, `ALL_DISTINCT (AK' [])`,
        `PERM _ obs'`, `(j,obs) = _`, `AM = _`, `AK = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `newAM [] = LUPDATE (SOME w) n (AM [])` by
    (gvs[dft_key_substitute_lupdate]) >>
  qpat_x_assum `newAM [] = MAP2 _ _ _` kall_tac >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`AM = _`, `AK = _`, `newAM = _`, `work = _`] >>
  qhdtm_x_assum `dft_focus_packet_rel` kall_tac >>
  conj_tac >- simp[] >> conj_tac
  >- (gvs[] >> irule dft_slot_fill_values >> simp[]) >>
  asm_rewrite_tac[] >> (metis_tac[dft_slot_fill_observation])
QED

Theorem dft_packet_closed_row_key[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e bb bt ps xs ys rho hin h0
    bentry count front brest ks key.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,bentry,count,front,T,brest) /\
  FLOOKUP ks_tab (a,e) = SOME ks /\ MEM key (FLAT ks) ==>
  (?cid. key = (a,e,cid)) \/
  ?cid sf tf inc entry order r8 rest.
    FLOOKUP acts ((e,cid)::a) = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) /\
    MEM key (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab ((e,cid)::a,f)))) order))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _`,
     `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        _ ==> _`,
     `!a e cid q h b0 done_at_call child_entry ret. FLOOKUP calls (a,e,cid) = _ ==> _`,
     `!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`,
     `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
        _ ==> !q. _`,
     `FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
     `AK = _`, `FLOOKUP blocks (a,e) = SOME _`,
     `FLOOKUP ks_tab (a,e) = SOME ks`, `MEM key (FLAT ks)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` drule >> strip_tac >>
  Cases_on `bentry`
  >- (qpat_x_assum `case NONE of NONE => _ | SOME v => _` mp_tac >> simp[] >>
      strip_tac >> gvs[]) >>
  PairCases_on `x` >>
  qpat_x_assum `case SOME _ of NONE => _ | SOME v => _`
    (strip_assume_tac o SRULE []) >>
  Cases_on `FLOOKUP ms_tab (a,e)`
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP ms_tab (a,e) = NONE`,`FDOM blocks = FDOM ms_tab`,
         `FLOOKUP blocks (a,e) = SOME _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[FLOOKUP_DEF]) >>
  rename1 `FLOOKUP ms_tab (a,e) = SOME ms` >>
  Cases_on `FLOOKUP es_tab (a,e)`
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP es_tab (a,e) = NONE`,`FDOM blocks = FDOM es_tab`,
         `FLOOKUP blocks (a,e) = SOME _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[FLOOKUP_DEF]) >>
  rename1 `FLOOKUP es_tab (a,e) = SOME ess` >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` drule >> simp[] >> strip_tac >>
  `?q. q < LENGTH xs /\ MEM key (EL q ks)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`MEM key (FLAT ks)`, `LENGTH xs = LENGTH ys`,
        `LENGTH ms = LENGTH ys`, `LENGTH ks = LENGTH ms`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[MEM_FLAT, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `!q. q < _ ==> _` (qspec_then `q` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL q xs).inst_opcode = GAS`
  >- (disj1_tac >> gvs[]) >>
  Cases_on `(EL q xs).inst_opcode = INVOKE`
  >- (`MEM q (TAKE count' rho')` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`PERM rho' (COUNT_LIST (LENGTH xs))`, `q < LENGTH xs`,
            `count' = LENGTH ys`, `LENGTH xs = LENGTH ys`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         drule sortingTheory.PERM_LENGTH >> drule sortingTheory.PERM_MEM_EQ >>
         simp[MEM_COUNT_LIST] >> rpt strip_tac >>
         gvs[rich_listTheory.LENGTH_COUNT_LIST, TAKE_LENGTH_TOO_LONG]) >>
      qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
        _ ==> !q. _` drule >> disch_then (qspec_then `q` mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. _ ==> _` drule >>
      strip_tac >>
      qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _`
        (qspec_then `(e,(EL q xs).inst_id)::a` mp_tac) >>
      simp[] >> strip_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`MEM key (EL q ks)`, `(EL q xs).inst_opcode = INVOKE`,
         `(EL q xs).inst_opcode = INVOKE ==> _`,
         `FLOOKUP calls (a,e,(EL q xs).inst_id) = _`,
         `FLOOKUP acts ((e,(EL q xs).inst_id)::a) = _`,
         `case SOME (ir,child_out,caller_post) of NONE => _ | SOME v => _`,
         `child_res = NONE <=> child_rest = NONE`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
      Cases_on `child_rest` >> gvs[] >> metis_tac[]) >>
  gvs[]
QED

Theorem dft_packet_completed_block[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) /\
  MEM e order ==>
  ?bb bt ps xs ys rho hin h0 bentry count front brest ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,bentry,count,front,T,brest) /\
    FLOOKUP ks_tab (a,e) = SOME ks
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`,
     `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _`,
     `FDOM blocks = FDOM ks_tab`, `MEM e order`,
     `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `(a,e) IN FDOM blocks` by
    (qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _`
       (mp_tac o cj 7) >> metis_tac[]) >>
  Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` drule >> strip_tac >>
  gvs[] >> Cases_on `e = LAST order` >> gvs[] >> metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]
QED

Theorem dft_packet_return_data:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  ~is_pseudo inst.inst_opcode ==>
  ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    LAST order = d /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    dft_fn_rel sf fn /\
    lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bt /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) rho ys /\
    bb_well_formed bt /\ count < LENGTH ys /\ inst = EL count ys /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK (TAKE count ys) be = OK s)
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`,
     `FLOOKUP acts p = _`, `LAST _ = d`, `FLOOKUP blocks (p,d) = _`,
     `get_instruction _ _ = _`, `case body_entry of NONE => _ | SOME v => _`,
     `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`,
     `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`,
     `LIST_REL (\f g. g = dft_fn f) _ _`, `o1_ctx_shape C8`,
     `~is_pseudo inst.inst_opcode`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` (drule_then strip_assume_tac) >> gvs[] >>
  Cases_on `body_entry`
  >- (gvs[venomInstTheory.get_instruction_def, EL_APPEND, EVERY_EL] >> metis_tac[]) >>
  PairCases_on `x` >> gvs[] >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _`
    (drule_then strip_assume_tac) >>
  `MEM fn C8.ctx_functions` by
    (drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  `wf_function fn` by metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM] >>
  `MEM bt fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def] >>
  `bb_well_formed bt` by metis_tac[venomWfTheory.wf_function_def] >>
  simp[] >> metis_tac[]
QED

Theorem dft_packet_return_geometry[local]:
  !sf tf bb bt ps xs ys count.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\ bb_well_formed bt /\
  (count:num) < LENGTH ys /\ is_terminator (EL count ys).inst_opcode ==>
  count + 1 = LENGTH ys /\ EL count ys = LAST xs /\ EL count ys = LAST ys /\
  xs <> [] /\ ys <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT xs) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT ys)
Proof
  map_every qx_gen_tac [`sf`,`tf`,`bb`,`bt`,`ps`,`xs`,`ys`,`ct`] >>
  strip_tac >> rename1 `ct < LENGTH ys` >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def] >>
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `LAST bt.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[dftRunRelTheory.dft_block_rel_last] >>
  drule_all dft_packet_body_shape >> strip_tac >>
  `ys <> [] /\ EVERY (\i. ~is_terminator i.inst_opcode) (FRONT ys)` by
    metis_tac[dft_packet_body_shape] >>
  `ct + 1 = LENGTH ys` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `ct < LENGTH ys` mp_tac >>
     qpat_assum `is_terminator (EL ct ys).inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[venomWfTheory.bb_well_formed_def] >>
     qpat_x_assum `!i. _ ==> _` (qspec_then `LENGTH ps + ct` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `ct = PRE (LENGTH ys)` by decide_tac >>
  qpat_x_assum `LAST bt.bb_instructions = LAST bb.bb_instructions` mp_tac >>
  simp[LAST_APPEND_NOT_NIL, GSYM LAST_EL]
QED

Theorem dft_packet_return_schedule[local]:
  !rho xs ys count.
  PERM rho (COUNT_LIST (LENGTH xs)) /\ LENGTH xs = LENGTH ys /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  count + 1 = LENGTH ys /\ (EL count ys).inst_opcode <> INVOKE ==>
  !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    MEM q (TAKE count rho)
Proof
  map_every qx_gen_tac [`schedule`,`xs`,`ys`,`ct`] >> strip_tac >>
  `LENGTH schedule = LENGTH ys` by metis_tac[LIST_REL_LENGTH] >>
  rpt strip_tac >>
  `MEM q schedule` by metis_tac[sortingTheory.PERM_MEM_EQ, MEM_COUNT_LIST] >>
  gvs[MEM_EL] >> rename1 `k < LENGTH ys` >>
  `k <= ct` by decide_tac >>
  `k <> ct` by
    (strip_tac >> gvs[] >>
     qpat_x_assum `LIST_REL _ schedule ys` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `ct` mp_tac) >> simp[] >>
     gvs[dftStructuralTheory.from_block_def, dftDefsTheory.is_flippable_def,
       venomEffectsTheory.is_commutative_def, passSharedDefsTheory.is_comparator_def,
       venomInstTheory.is_pseudo_def] >> rpt strip_tac >> gvs[]) >>
  simp[MEM_EL] >> qexists `k` >> simp[EL_TAKE]
QED

Theorem dft_packet_return_cursor:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    fuel ir child_out.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  step_inst fuel C8 inst s = IntRet ir child_out ==>
  ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    LAST order = d /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    LENGTH xs = LENGTH ys /\ count + 1 = LENGTH ys /\
    inst = LAST xs /\ inst = LAST ys /\ xs <> [] /\ ys <> [] /\
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT xs) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT ys) /\
    MEM inst.inst_opcode [RET; RETFMP; DRET] /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK (TAKE count ys) be = OK s) /\
    (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
      MEM q (TAKE count rho) /\
      ?call_h b0 done child_entry ir' out post.
        FLOOKUP calls (p,d,(EL q xs).inst_id) =
          SOME (q,call_h,b0,done,child_entry,SOME (ir',out,post)))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst.inst_opcode [RET; RETFMP; DRET]` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
         simp[Once venomExecSemanticsTheory.step_inst_def] >>
         gvs[AllCaseEqs(), venomExecSemanticsTheory.bind_outputs_def]) >>
     fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
     drule opcodeClassTheory.step_inst_base_intret_opcodes >> simp[] >> metis_tac[]) >>
  `~is_pseudo inst.inst_opcode /\ is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE` by
    gvs[venomInstTheory.is_pseudo_def, venomInstTheory.is_terminator_def] >>
  drule_all dft_packet_return_data >> strip_tac >>
  rename1 `inst = EL ct ys` >>
  rename1 `PERM schedule (COUNT_LIST (LENGTH xs))` >>
  `is_terminator (EL ct ys).inst_opcode` by metis_tac[] >>
  drule_all dft_packet_return_geometry >> strip_tac >>
  `!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
    MEM q (TAKE ct schedule)` by
    metis_tac[dft_packet_return_schedule] >>
  qexistsl [`sf`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,`schedule`,
    `in_state`,`h0`,`be`,`hbe`,`ct`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `MEM q (TAKE ct schedule)` by metis_tac[] >>
  metis_tac[dft_packet_completed_call]
QED

Theorem dft_packet_return_target_row:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    fuel ir child_out bb bt ps xs ys rho in_state h0 be hbe count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  step_inst fuel C8 inst s = IntRet ir child_out /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) ==>
  !F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = IntRet ir child_out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_return_cursor >> strip_tac >> gvs[] >>
  rename1 `ct + 1 = LENGTH ys` >>
  `ct = PRE (LENGTH ys)` by decide_tac >>
  `TAKE ct ys = FRONT ys` by simp[TAKE_PRE_LENGTH] >>
  `ys = FRONT ys ++ [LAST ys]` by simp[APPEND_FRONT_LAST] >>
  `(LAST xs).inst_opcode <> INVOKE` by simp[] >>
  qx_gen_tac `budget` >> strip_tac >>
  `step_inst (budget-LAST order) C8 (LAST xs) s = IntRet ir child_out` by
    fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `FOLDR (dft_exec_cons (budget-LAST order) C8) OK (FRONT ys) be = OK s` by metis_tac[] >>
  qpat_assum `ys = FRONT ys ++ _` (fn th => once_rewrite_tac [th]) >>
  irule dftPacketReturnLocalTheory.dft_packet_fold_intret >> simp[] >> metis_tac[]
QED

Theorem dft_packet_closed_row_data[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order result rest
    e bb bt ps xs ys rho hin h0 be hbe count front brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME result,SOME rest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,T,brest) ==>
  e <= N /\ lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  be.vs_current_bb = bb.bb_label /\ count = LENGTH ys /\ LENGTH ys = LENGTH xs /\
  PERM rho (COUNT_LIST (LENGTH xs)) /\ IS_SOME brest /\ bb_well_formed bb /\
  (e <> LAST order ==> ?post. front = OK post /\ ~post.vs_halted) /\
  (e = LAST order ==> front = result)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`,
     `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _`,
     `o1_ctx_shape C7`,
     `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME result,SOME rest)`,
     `FLOOKUP blocks (a,e) = SOME _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest. _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `FLOOKUP acts a = SOME (_,_,_,_,_,SOME result,SOME rest)`
    (fn th => qpat_x_assum `FLOOKUP acts a = SOME _`
      (mp_tac o REWRITE_RULE [th])) >>
  simp_tac (srw_ss()) [] >>
  disch_then (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS) >>
  rename1 `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,_,ct,_,_,_)` >>
  qpat_x_assum `case SOME (be,hbe) of NONE => _ | SOME v => _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`e <= N`, `lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb`,
     `bt.bb_instructions = ps ++ ys`, `be.vs_inst_idx = LENGTH ps`,
     `be.vs_current_bb = bb.bb_label`, `ct = LENGTH ys`,
     `LENGTH xs = LENGTH ys`, `PERM _ (COUNT_LIST (LENGTH xs))`,
     `T <=> IS_SOME brest`, `e <> LAST order ==> _`,
     `e = LAST order ==> _`, `MEM sf C7.ctx_functions`,
     `o1_ctx_shape C7`, `lookup_block bb.bb_label sf.fn_blocks = SOME bb`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >> rpt strip_tac >>
  `wf_function sf` by
    metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def] >>
  metis_tac[venomWfTheory.wf_function_def]
QED

Theorem dft_packet_closed_suffix_row:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME result,SOME rest) /\
  r < LENGTH order ==>
  ?e bb bt ps xs ys rho hin h0 be hbe count front brest ms ess ks sp.
    e = EL r order /\ e = inc + SUC r /\ e <= N /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,T,SOME brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks /\
    lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT xs) /\
    be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
    count = LENGTH ys /\ LENGTH ys = LENGTH xs /\
    PERM rho (COUNT_LIST (LENGTH xs)) /\
    (!q. q < LENGTH xs ==> MEM q (TAKE count rho)) /\
    eval_phis hin (ps ++ ys) = OK sp /\
    (!fuel. FOLDR (dft_exec_cons (fuel-e) C8) OK
      (DROP (phi_prefix_length (ps ++ ys)) ps)
      (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be) /\
    (r = 0 ==> hin = entry) /\
    (SUC r < LENGTH order ==>
      ?post nb nt nps nxs nys nrho nh0 nbody nc nf nclosed nr.
        front = OK post /\ ~post.vs_halted /\
        FLOOKUP blocks (a,EL (SUC r) order) =
          SOME (nb,nt,nps,nxs,nys,nrho,post,nh0,nbody,nc,nf,nclosed,nr)) /\
    (SUC r = LENGTH order ==> front = result /\ ?ir out. result = IntRet ir out) /\
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks
Proof
  strip_tac >>
  `MEM (EL r order) order` by simp[EL_MEM] >>
  drule_all dft_packet_completed_block >> strip_tac >>
  `bentry <> NONE` by (drule_all dft_packet_selected_input >> simp[]) >>
  Cases_on `bentry` >> gvs[] >> PairCases_on `x` >>
  drule_all dft_packet_selected_body >> strip_tac >>
  drule_all dft_packet_closed_row_data >> strip_tac >>
  drule_all dft_packet_body_shape >> strip_tac >>
  drule_all dft_packet_closed_activation_return >> strip_tac >>
  `order = GENLIST (\i. inc + SUC i) (LENGTH order)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
       MEM sf C7.ctx_functions /\ _` (mp_tac o cj 6) >>
     qpat_x_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME result,SOME rest)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!i. i < LENGTH order ==> EL i order = inc + SUC i` by
    (rpt strip_tac >> qpat_assum `order = GENLIST _ _`
       (fn th => once_rewrite_tac[th]) >> simp[EL_GENLIST]) >>
  `EL r order = inc + SUC r` by simp[] >>
  `?ms ess. FLOOKUP ms_tab (a,EL r order) = SOME ms /\
    FLOOKUP es_tab (a,EL r order) = SOME ess /\
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks` by
    suspend "row_arrays" >>
  Cases_on `brest` >> gvs[] >>
  rpt conj_tac
  >- suspend "done_indices"
  >- suspend "first_input"
  >- suspend "next_input"
  >- suspend "last_result"
QED

Resume dft_packet_closed_suffix_row[row_arrays]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
     `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
       _ ==> _`,
     `FLOOKUP blocks (a,EL r order) = SOME _`,
     `FLOOKUP ks_tab (a,EL r order) = SOME ks`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  Cases_on `FLOOKUP ms_tab (a,EL r order)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP es_tab (a,EL r order)` >- gvs[FLOOKUP_DEF] >>
  map_every (fn n =>
    qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
      _ ==> _` (mp_tac o cj n)) [1,2,3,4,5] >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` kall_tac >> rpt strip_tac >> simp[] >> metis_tac[]
QED
Resume dft_packet_closed_suffix_row[done_indices]:
  qpat_assum `PERM rho' (COUNT_LIST (LENGTH xs))` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> drule sortingTheory.PERM_MEM_EQ >>
  simp[MEM_COUNT_LIST, rich_listTheory.LENGTH_COUNT_LIST] >>
  rpt strip_tac >> gvs[TAKE_LENGTH_TOO_LONG]
QED
Resume dft_packet_closed_suffix_row[first_input]:
  strip_tac >> drule_all dft_packet_selected_input >> gvs[]
QED
Resume dft_packet_closed_suffix_row[next_input]:
  strip_tac >>
  `order <> []` by (Cases_on `order` >> gvs[]) >>
  `LAST order = inc + LENGTH order` by
    (simp[LAST_EL] >>
     `PRE (LENGTH order) < LENGTH order` by decide_tac >>
     simp[] >> decide_tac) >>
  `inc + SUC r <> LAST order` by decide_tac >>
  `?post. front = OK post /\ ~post.vs_halted` by metis_tac[] >>
  qpat_x_assum `MEM (inc + SUC r) order` kall_tac >>
  `MEM (EL (SUC r) order) order` by simp[EL_MEM] >>
  drule_all dft_packet_completed_block >> strip_tac >>
  qpat_x_assum `FLOOKUP blocks (a,inc + SUC r) = SOME _` mp_tac >>
  drule_all dft_packet_selected_input >>
  `EL (SUC r) order = inc + SUC (SUC r)` by simp[] >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  `inc + SUC (SUC r) - 1 = inc + SUC r` by decide_tac >> gvs[]
QED
Resume dft_packet_closed_suffix_row[last_result]:
  strip_tac >>
  `order <> []` by (Cases_on `order` >> gvs[]) >>
  `LAST order = inc + SUC r` by
    (simp[LAST_EL] >>
     `PRE (LENGTH order) = r` by decide_tac >> simp[]) >>
  gvs[]
QED
Finalise dft_packet_closed_suffix_row

Theorem dft_packet_closed_suffix_keys_ind[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  !n F a sf tf inc entry order r8 rest r bb bt ps xs ys rho hin h0 body count front closed brest gs tail.
  n = F - (inc+r) /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) /\
  r < LENGTH order /\
  FLOOKUP blocks (a,EL r order) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
  N <= F /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) (DROP r order))) gs ==>
  ?extra. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) (DROP r order)) =
    MAP FST (trace_gas (trace_blocks a (inc+r) (F-(inc+r)) C7 sf
      (hin with vs_gas_readings := gs ++ tail))) ++ extra
Proof
  strip_tac >> completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  rename1 `N <= fuel` >>
  drule_all dft_packet_closed_suffix_row >> strip_tac >>
  `EL r order = inc + SUC r` by metis_tac[] >>
  gvs[] >>
  `DROP r order = (inc + SUC r)::DROP (SUC r) order` by
    metis_tac[DROP_CONS_EL] >>
  qpat_x_assum `LIST_REL _ (FLAT _) gs` mp_tac >>
  simp[] >> rewrite_tac[LIST_REL_SPLIT1] >> strip_tac >> gvs[] >>
  rename1 `LIST_REL _ (FLAT ms) rowgs` >>
  rename1 `LIST_REL _ (FLAT (MAP _ (DROP (SUC r) order))) latergs` >>
  `?kgss. rowgs = FLAT kgss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms kgss` by
    metis_tac[dft_packet_flat_filling_split] >>
  `?sp'. eval_phis (hin with vs_gas_readings := rowgs ++ latergs ++ tail)
      (ps ++ xs) = OK sp' /\
    FOLDR (dft_exec_cons (fuel-(inc+SUC r)) C7) OK
      (DROP (phi_prefix_length (ps ++ xs)) ps)
      (sp' with vs_inst_idx := phi_prefix_length (ps ++ xs)) =
      OK (be with vs_gas_readings := rowgs ++ latergs ++ tail)` by
    (irule dft_packet_body_entry_replay >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl [`C8`,`fuel-(inc+SUC r)`] >> simp[]) >>
  `LIST_REL (\i keys.
    if i.inst_opcode = GAS then keys = [(a,inc+SUC r,i.inst_id)]
    else if i.inst_opcode = INVOKE then T else keys = []) xs ks` by
    suspend "row_key_shape" >>
  `fuel - (inc+SUC r) < fuel - (inc+r)` by decide_tac >>
  `?extra. FLAT ks = MAP FST (trace_gas
    (trace_block a (inc+SUC r) (fuel-(inc+SUC r)) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
      (be with vs_gas_readings := rowgs ++ latergs ++ tail))) ++ extra` by
    (irule dft_packet_native_row_keys >> qexists_tac `xs` >> simp[] >>
     (reverse conj_tac >- simp[DROP_APPEND]) >>
     rpt gen_tac >> strip_tac >>
     irule dft_packet_call_supplier_from_child >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = _` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,inc+SUC r) = _` (irule_at Any) >>
     qpat_assum `FLOOKUP ms_tab (a,inc+SUC r) = _` (irule_at Any) >>
     qexistsl [`latergs ++ tail`,`kgss`] >>
     simp[] >> suspend "child_coverage") >>
  suspend "suffix_continuation"
QED

Resume dft_packet_closed_suffix_keys_ind[row_key_shape]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` drule >> simp[] >> strip_tac >>
  qpat_x_assum `!sf tf inc entry order res nrest. _` drule >>
  strip_tac >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  qpat_x_assum `!q. q < LENGTH xs ==>
    (((EL q xs).inst_opcode = GAS ==> _) /\ _ /\ _)`
    (qspec_then `n` mp_tac) >> simp[] >>
  Cases_on `(EL n xs).inst_opcode = GAS` >> simp[] >>
  Cases_on `(EL n xs).inst_opcode = INVOKE` >> simp[]
QED

Resume dft_packet_closed_suffix_keys_ind[child_coverage]:
  rpt gen_tac >> strip_tac >>
  `corder <> []` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
       (mp_tac o cj 5) >>
     qpat_assum `FLOOKUP acts ((inc+SUC r,_)::a) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `0 < LENGTH corder` by (Cases_on `corder` >> gvs[]) >>
  drule_all dft_packet_closed_suffix_row >> strip_tac >>
  qpat_x_assum `!m. m < fuel - (inc+r) ==> _`
    (qspec_then `fuel-(inc+SUC r)` mp_tac) >>
  simp[] >> disch_then (qspec_then `fuel` mp_tac) >>
  disch_then (drule_at (Pat `FLOOKUP acts _ = _`)) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[EL]
QED
Resume dft_packet_closed_suffix_keys_ind[suffix_continuation]:
  `phi_prefix_length (ps ++ xs) <= LENGTH ps` by
    (`EVERY (\i. i.inst_opcode <> PHI) xs` by
       (gvs[EVERY_MEM] >> metis_tac[venomInstTheory.is_pseudo_def]) >>
     simp[dftIndexedExecTheory.dft_phi_prefix_append,
       venomExecProofsTheory.phi_prefix_length_le]) >>
  `phi_prefix_length (ps ++ xs) - LENGTH ps = 0` by decide_tac >>
  `fuel - (inc+r) = SUC (fuel - (inc+SUC r))` by decide_tac >>
  qmatch_asmsub_abbrev_tac `FOLDR _ OK _ start = OK bs` >>
  `DROP start.vs_inst_idx bb.bb_instructions =
     DROP (phi_prefix_length (ps ++ xs)) ps ++ xs` by
    simp[Abbr `start`, DROP_APPEND] >>
  `TAKE (LENGTH ps - phi_prefix_length (ps ++ xs))
     (DROP start.vs_inst_idx bb.bb_instructions) =
     DROP (phi_prefix_length (ps ++ xs)) ps` by
    simp[TAKE_APPEND, LENGTH_DROP] >>
  `trace_gas (trace_block a (inc+SUC r) (fuel-(inc+SUC r)) C7 sf bb start) =
   trace_gas (trace_block a (inc+SUC r) (fuel-(inc+SUC r)) C7 sf bb bs)` by
    (irule native_trace_block_pseudo_skip >>
     qexists_tac `LENGTH ps - phi_prefix_length (ps ++ xs)` >>
     simp[Abbr `start`, EVERY_DROP]) >>
  `trace_block a (inc+SUC r) (fuel-(inc+SUC r)) C7 sf bb bs =
     trace_block a (inc+SUC r) (fuel-(inc+SUC r)) C7 sf
       <|bb_label := be.vs_current_bb; bb_instructions :=
         REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> bs` by
    (irule native_trace_block_suffix_cong >> simp[Abbr `bs`, DROP_APPEND]) >>
  `exec_block (fuel-(inc+SUC r)) C7 bb start =
     FOLDR (dft_exec_cons (fuel-(inc+SUC r)) C7) OK xs bs` by
    (irule EQ_TRANS >>
     qexists_tac `exec_block (fuel-(inc+SUC r)) C7 bb bs` >>
     conj_tac
     >- (irule native_exec_block_prefix_skip >>
         qexists_tac `LENGTH ps - phi_prefix_length (ps ++ xs)` >>
         simp[Abbr `start`] >>
         irule EVERY_MONOTONIC >> qexists_tac `\i. is_pseudo i.inst_opcode` >>
         simp[EVERY_DROP] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
         simp[venomInstTheory.is_pseudo_def, venomInstTheory.is_terminator_def]) >>
     irule native_exec_block_terminated_fold >>
     simp[Abbr `bs`, DROP_APPEND]) >>
  qpat_assum `fuel - (inc+r) = SUC _` (fn th => once_rewrite_tac[th]) >>
  once_rewrite_tac[trace_defs] >>
  gvs[Abbr `start`] >>
  rewrite_tac[dftGasFromListReadingsTheory.trace_gas_append, MAP_APPEND] >>
  `SUC (inc+r) = inc+SUC r` by decide_tac >>
  qpat_assum `SUC (inc+r) = inc+SUC r`
    (fn th => pure_once_rewrite_tac[th]) >>
  qpat_assum `trace_gas (trace_block _ _ _ _ _ bb _) = _`
    (fn th => rewrite_tac[th]) >>
  qpat_assum `trace_block _ _ _ _ _ bb bs = _`
    (fn th => rewrite_tac[th]) >>
  Cases_on `FOLDR (dft_exec_cons (fuel-(inc+SUC r)) C7) OK xs bs` >>
  simp[GSYM dftGasFromListTraceDefsTheory.trace_gas_def, APPEND_ASSOC] >>
  rename1 `FOLDR _ OK xs bs = OK source_post` >>
  `MAP FST (trace_gas (trace_block a (inc+SUC r) (fuel-(inc+SUC r)) C7 sf
     <|bb_label := be.vs_current_bb; bb_instructions :=
       REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> bs)) = FLAT ks` by
    (qunabbrev_tac `bs` >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     irule dft_packet_closed_row_key_success >>
     conj_tac >- metis_tac[APPEND_ASSOC] >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `source_post.vs_halted`
  >- simp[dftGasFromListTraceDefsTheory.trace_gas_def] >>
  `SUC r <= LENGTH order` by decide_tac >>
  `(?post. front = OK post) \/ (?ir out. front = IntRet ir out)` by
    (Cases_on `SUC r < LENGTH order` >- metis_tac[] >>
     `SUC r = LENGTH order` by decide_tac >> metis_tac[]) >>
  `residual_result (latergs ++ tail) front (OK source_post)` by
    (qpat_assum `FOLDR _ OK xs bs = OK source_post`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     qunabbrev_tac `bs` >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     irule dft_packet_closed_row_residual >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,inc+SUC r) = SOME _` (irule_at Any) >>
     simp[] >> qexists_tac `fuel-(inc+SUC r)` >>
     simp[APPEND_ASSOC, passSimulationDefsTheory.terminates_def]) >>
  gvs[dftGasToListReplayTheory.residual_result_def, stateEquivTheory.lift_result_def] >>
  `SUC r < LENGTH order` by
    (Cases_on `SUC r = LENGTH order` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `SUC r < LENGTH order ==> _` (drule_then strip_assume_tac) >>
  gvs[]
QED
Finalise dft_packet_closed_suffix_keys_ind

Theorem dft_packet_closed_suffix_keys:
  !F a sf tf inc entry order r8 rest r bb bt ps xs ys rho hin h0 body count front closed brest gs tail.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) /\
  r < LENGTH order /\
  FLOOKUP blocks (a,EL r order) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
  N <= F /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) (DROP r order))) gs ==>
  ?extra. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) (DROP r order)) =
    MAP FST (trace_gas (trace_blocks a (inc+r) (F-(inc+r)) C7 sf
      (hin with vs_gas_readings := gs ++ tail))) ++ extra
Proof
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  drule dft_packet_closed_suffix_keys_ind >>
  disch_then (qspec_then `fuel-(inc+r)` mp_tac) >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem dft_packet_closed_keys:
  !F a sf tf inc entry order r8 rest gs tail.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) /\
  N <= F /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) order)) gs ==>
  ?extra. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order) =
    MAP FST (trace_gas (trace_blocks a inc (F-inc) C7 sf
      (entry with vs_gas_readings := gs ++ tail))) ++ extra
Proof
  rpt gen_tac >> strip_tac >>
  `order <> []` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
       (mp_tac o cj 5) >>
     qpat_assum `FLOOKUP acts a = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `0 < LENGTH order` by (Cases_on `order` >> gvs[]) >>
  drule_all dft_packet_closed_suffix_row >> strip_tac >>
  drule_at (Pat `r < LENGTH order`) dft_packet_closed_suffix_keys >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >> gvs[] >>
  metis_tac[]
QED

Theorem dft_packet_call_supplier:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks F q kgss tail u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME(sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME(bb,bt,ps,xs,ys,rho,hin,h0,SOME(be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= F /\ q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
  MEM q (TAKE count rho) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms kgss /\
  FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
  (?extra. EL q ks = MAP FST (trace_gas
    (trace_step a e (F-e) C7 sf (EL q xs) u)) ++ extra) /\
  (!v. step_inst (F-e) C7 (EL q xs) u = OK v ==>
    EL q ks = MAP FST (trace_gas (trace_step a e (F-e) C7 sf (EL q xs) u)))
Proof
  rpt gen_tac >> strip_tac >>
  irule dft_packet_call_supplier_from_child >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP ms_tab (a,e) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP ks_tab (a,e) = _` (irule_at Any) >>
  qexistsl [`tail`,`kgss`] >> simp[] >>
  rpt gen_tac >> strip_tac >> irule dft_packet_closed_keys >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem dft_packet_row_cut_keys:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks F k kgss tail.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  N <= F /\ k <= LENGTH xs /\
  (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
  ?extra. FLAT (TAKE k ks) = MAP FST (trace_gas
    (trace_block a e (F-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail))) ++ extra
Proof
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  `LENGTH ms = LENGTH xs /\ LENGTH ks = LENGTH xs /\
   LIST_REL (\i keys.
     if i.inst_opcode = GAS then keys = [(a,e,i.inst_id)]
     else if i.inst_opcode = INVOKE then T else keys = []) xs ks` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
       (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
        qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
       FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
       FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
       (drule_all_then strip_assume_tac) >>
     qpat_x_assum `!sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
     simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_x_assum `!q. q < LENGTH xs ==> _` (drule_then strip_assume_tac) >>
     Cases_on `(EL n xs).inst_opcode = GAS` >> simp[] >>
     Cases_on `(EL n xs).inst_opcode = INVOKE` >> simp[]) >>
  irule dft_packet_native_row_keys >> qexists_tac `TAKE k xs` >>
  simp[DROP_APPEND] >>
  reverse conj_tac
  >- (qpat_assum `LIST_REL _ xs ks`
        (mp_tac o Q.SPEC `k` o MATCH_MP LIST_REL_TAKE) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[LENGTH_TAKE, EL_TAKE, TAKE_TAKE] >>
  irule dft_packet_call_from_child_prefix >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP ms_tab (a,e) = _` (irule_at Any) >>
  qpat_assum `FLOOKUP ks_tab (a,e) = _` (irule_at Any) >>
  qexistsl [`tail`,`kgss`,`k`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule dft_packet_closed_keys >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem dft_packet_closed_activation_key_absent:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) ==>
  !f cid. ~MEM (p,f,cid)
    (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order))
Proof
  strip_tac >>
  `?lsf ltf linc lent lo.
    FLOOKUP acts p = SOME (lsf,ltf,linc,lent,lo,NONE,NONE)` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     goal_assum (drule_at Any)) >>
  `?B. !a. a IN FDOM acts ==> LENGTH a <= B` by
    (irule iterateTheory.UPPER_BOUND_FINITE_SET >> simp[]) >>
  qsuff_tac `!n a sf tf inc entry order r8 rest.
    n = B - LENGTH a /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) ==>
    !f cid. ~MEM (p,f,cid)
      (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order))`
  >- metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  rename1 `FLOOKUP acts aa = SOME (asf,atf,ainc,aent,aorder,SOME ar8,SOME arest)` >>
  `?e. MEM e aorder /\ MEM (p,f,cid) (FLAT (THE (FLOOKUP ks_tab (aa,e))))` by
    (qpat_x_assum `MEM _ (FLAT _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[MEM_FLAT, MEM_MAP] >>
     rpt strip_tac >> gvs[] >> metis_tac[MEM_FLAT]) >>
  drule_all dft_packet_completed_block >> strip_tac >>
  `MEM (p,f,cid) (FLAT ks)` by gvs[] >>
  drule_all dft_packet_closed_row_key >> strip_tac
  >- gvs[] >>
  `((e,cid')::aa) IN FDOM acts` by
    (Cases_on `((e,cid')::aa) IN FDOM acts` >> gvs[FLOOKUP_DEF]) >>
  `SUC (LENGTH aa) <= B` by
    (qpat_x_assum `!a. a IN FDOM acts ==> _`
       (qspec_then `(e,cid')::aa` mp_tac) >> simp[]) >>
  `B - LENGTH ((e,cid')::aa) < n` by (simp[] >> decide_tac) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `B - LENGTH ((e,cid')::aa)` mp_tac) >>
  simp[] >> qexists_tac `(e,cid')::aa` >> simp[] >> metis_tac[]
QED

Theorem dft_packet_closed_block_key_absent:
  !rho count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb0,bt0,ps0,xs0,ys0,rho0,hin0,h00,bentry0,count0,front0,F,brest0) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,bentry,count,front,T,brest) /\
  FLOOKUP ks_tab (a,e) = SOME ks ==>
  !cid. ~MEM (p,d,cid) (FLAT ks)
Proof
  strip_tac >> rpt strip_tac >>
  drule_all dft_packet_closed_row_key >> strip_tac
  >- gvs[] >>
  drule_all dft_packet_closed_activation_key_absent >> metis_tac[]
QED

Theorem dft_packet_key_rows_unchanged[local]:
  !rows keyrows needle w.
  LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keyrows /\
  ~MEM needle (FLAT keyrows) ==>
  MAP2 (\ss kk. MAP2 (\slot key. if key = needle then SOME w else slot) ss kk)
    rows keyrows = rows
Proof
  Induct >> Cases_on `keyrows` >> simp[] >> rpt strip_tac >>
  gvs[dft_key_substitute_shape]
QED

Theorem dft_packet_closed_keymap_row[local]:
  !rho count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb0,bt0,ps0,xs0,ys0,rho0,hin0,h00,bentry0,count0,front0,F,brest0) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,bentry,count,front,T,brest) /\
  work = FMAP_MAP2 (\(ae,rows).
    MAP2 (\ss kk. MAP2 (\slot key.
      if key = (p,d,cid) then SOME w else slot) ss kk)
      rows (THE (FLOOKUP ks_tab ae))) ms_tab ==>
  FLOOKUP work (a,e) = FLOOKUP ms_tab (a,e)
Proof
  rpt strip_tac >>
  `FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM ks_tab` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
     qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  Cases_on `FLOOKUP ms_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  rename1 `FLOOKUP ms_tab (a,e) = SOME rows` >>
  Cases_on `FLOOKUP ks_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  rename1 `FLOOKUP ks_tab (a,e) = SOME keys` >>
  drule_all dft_packet_table_row_alignment >> disch_tac >>
  drule_all dft_packet_closed_block_key_absent >> disch_tac >>
  simp[FLOOKUP_FMAP_MAP2] >> irule dft_packet_key_rows_unchanged >> simp[]
QED

Theorem dft_packet_closed_keymap_unchanged:
  !rho0 count0.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (p,d) =
    SOME (bb0,bt0,ps0,xs0,ys0,rho0,hin0,h00,bentry0,count0,front0,F,brest0) /\
  work = FMAP_MAP2 (\(ae,rows).
    MAP2 (\ss kk. MAP2 (\slot key.
      if key = (p,d,cid) then SOME w else slot) ss kk)
      rows (THE (FLOOKUP ks_tab ae))) ms_tab ==>
  (!a e bb bt ps xs ys rho hin h0 bentry count front brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,bentry,count,front,T,brest) ==>
    FLOOKUP work (a,e) = FLOOKUP ms_tab (a,e)) /\
  (!a sf tf inc entry order r8 rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME rest) ==>
    FLAT (MAP (\e. FLAT (THE (FLOOKUP work (a,e)))) order) =
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) order))
Proof
  rpt strip_tac
  >- (irule dft_packet_closed_keymap_row >> metis_tac[]) >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
  drule_all dft_packet_completed_block >> strip_tac >>
  drule_all dft_packet_closed_keymap_row >> simp[]
QED

Theorem dft_packet_ordinary_invoke_members[local]:
  !n rho xs.
  n < LENGTH rho /\ (EL (EL n rho) xs).inst_opcode <> INVOKE ==>
  !q. (EL q xs).inst_opcode = INVOKE ==>
    (MEM q (TAKE (SUC n) rho) <=> MEM q (TAKE n rho))
Proof
  rpt strip_tac >> simp[TAKE_SUC_BY_TAKE, MEM_SNOC] >> metis_tac[]
QED

Theorem dft_packet_ordinary_prefix_extend[local]:
  !ys n be s inst post fuel C fuel'.
  n < LENGTH ys /\ inst = EL n ys /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE n ys) /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK post /\
  FOLDR (dft_exec_cons fuel' C) OK (TAKE n ys) be = OK s ==>
  FOLDR (dft_exec_cons fuel' C) OK (TAKE (SUC n) ys) be =
    OK (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `step_inst fuel' C inst s = OK post` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  simp[TAKE_SUC_BY_TAKE, SNOC_APPEND, FOLDR_APPEND] >>
  drule_all dftRunRelTheory.dft_exec_prefix_continue >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def]
QED

Theorem dft_packet_aligned_map2_take[local]:
  !q ss kk H. LENGTH ss = LENGTH kk ==>
    TAKE q (MAP2 H ss kk) = MAP2 H (TAKE q ss) (TAKE q kk)
Proof
  Induct_on `q` >> Cases_on `ss` >> Cases_on `kk` >> simp[MAP2]
QED

Theorem dft_packet_flat_map2[local]:
  !cs M K W H.
    (!x. MEM x cs ==> W x = MAP2 H (M x) (K x) /\
      LENGTH (M x) = LENGTH (K x)) ==>
    FLAT (MAP W cs) = MAP2 H (FLAT (MAP M cs)) (FLAT (MAP K cs)) /\
    LENGTH (FLAT (MAP M cs)) = LENGTH (FLAT (MAP K cs))
Proof
  Induct_on `cs` >> simp[] >>
  map_every qx_gen_tac [`x0`,`mf`,`kf`,`wfun`,`hfun`] >> strip_tac >>
  first_x_assum (qspecl_then [`mf`,`kf`,`wfun`,`hfun`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[MAP2_APPEND] >> metis_tac[]
QED

Theorem dft_packet_keymap_cut_piece[local]:
  !H M Ktab W a ds e q.
    W = FMAP_MAP2 (\(ae,rows).
      MAP2 (\ss kk. MAP2 H ss kk) rows (THE (FLOOKUP Ktab ae))) M /\
    (!f. MEM f (e::ds) ==> ?rows keys.
      FLOOKUP M (a,f) = SOME rows /\ FLOOKUP Ktab (a,f) = SOME keys /\
      LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keys) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP W (a,f)))) ds) ++
      FLAT (TAKE q (THE (FLOOKUP W (a,e)))) =
    MAP2 H
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP M (a,f)))) ds) ++
        FLAT (TAKE q (THE (FLOOKUP M (a,e)))))
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP Ktab (a,f)))) ds) ++
        FLAT (TAKE q (THE (FLOOKUP Ktab (a,e))))) /\
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP M (a,f)))) ds) ++
        FLAT (TAKE q (THE (FLOOKUP M (a,e))))) =
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP Ktab (a,f)))) ds) ++
        FLAT (TAKE q (THE (FLOOKUP Ktab (a,e)))))
Proof
  rpt gen_tac >> strip_tac >>
  `?rows keys. FLOOKUP M (a,e) = SOME rows /\
    FLOOKUP Ktab (a,e) = SOME keys /\
    LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keys` by metis_tac[MEM] >>
  `LIST_REL (\ss kk. LENGTH ss = LENGTH kk) (TAKE q rows) (TAKE q keys)` by
    metis_tac[EVERY2_TAKE] >>
  `!f. MEM f ds ==> LENGTH (FLAT (THE (FLOOKUP M (a,f)))) =
      LENGTH (FLAT (THE (FLOOKUP Ktab (a,f))))` by
    (rpt strip_tac >> first_x_assum (qspec_then `f` mp_tac) >>
     simp[] >> strip_tac >> simp[] >>
     irule dft_key_map_flat_length >> simp[]) >>
  `LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP M (a,f)))) ds)) =
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP Ktab (a,f)))) ds))` by
    (simp[LENGTH_FLAT,MAP_MAP_o] >> AP_TERM_TAC >>
     irule MAP_CONG >> simp[]) >>
  `LENGTH (FLAT (TAKE q rows)) = LENGTH (FLAT (TAKE q keys))` by
    metis_tac[dft_key_map_flat_length] >>
  drule dft_key_map_order_flat >>
  disch_then (qspecl_then [`a`,`ds`] mp_tac) >>
  (impl_tac >- metis_tac[MEM]) >> strip_tac >>
  `LENGTH rows = LENGTH keys` by metis_tac[LIST_REL_LENGTH] >>
  simp[FLOOKUP_FMAP_MAP2,dft_packet_aligned_map2_take,
    dft_key_map_flat,MAP2_APPEND]
QED

Theorem dft_packet_body_next_transport:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst s oms om hs h raw_slots sites unused
    bb bt ps xs ys rho in_state h0 be hbe count fuel post inst' q8' es0.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  (inst.inst_opcode = GAS ==> s.vs_gas_readings <> []) /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C8 inst s = OK post /\
  active_inst fn inst' (post with vs_inst_idx := SUC s.vs_inst_idx) /\
  q8' = JointConfig stk PG (step_prov PG G inst post)
    (step_taint inst s post tn) fn inst'
    (post with vs_inst_idx := SUC s.vs_inst_idx) oms (origin_step PG om inst post) hs
    (h ++ [OriginOrdinary fuel post; OriginObserve
      (OriginSnapshot fn PG (step_prov PG G inst post) (origin_step PG om inst post)
        inst' (post with vs_inst_idx := SUC s.vs_inst_idx))]) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
  inst' = EL (SUC count) ys /\
  SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,inst'.inst_id),fn,inst',post with vs_inst_idx := SUC s.vs_inst_idx) /\
  TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
    TAKE j (trace_blocks [] 0 N C8 root_tf root_entry) ++ [((p,d,inst.inst_id),fn,inst,s)] /\
  (!F kgss tail q u orc.
    N <= F /\ q < LENGTH xs /\ EL q xs = inst' /\
    inv_memory_observation inst'.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    FOLDR (dft_exec_cons (F-d) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
    FOLDR (dft_exec_cons (N-d) C8) OK (TAKE (SUC count) ys) be =
      OK (post with vs_inst_idx := SUC s.vs_inst_idx) /\
    trace_agrees orc (trace_block p d (F-d) C7
      (FST (THE (FLOOKUP acts p)))
      (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
      (be with vs_gas_readings := FLAT kgss ++ tail)) /\
    trace_agrees orc (trace_block p d (N-d) C8 fn
      (bt with bb_instructions := TAKE (LENGTH ps + SUC count) bt.bb_instructions) be) ==>
    (!op. MEM op inst'.inst_operands ==>
      eval_operand op u = eval_operand op (post with vs_inst_idx := SUC s.vs_inst_idx)) /\
    u.vs_initial_fmp = (post with vs_inst_idx := SUC s.vs_inst_idx).vs_initial_fmp) ==>
  ?N' obs' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d'
    raw_slots' sites' unused'.
    N <= N' /\
    dft_focus_packet_rel N' C7 C8 root_sf root_tf root_entry
      (SUC j,obs')
      acts' blocks' calls' ms_tab' es_tab' ks_tab' rooted_eval p' d'
      q8' raw_slots' sites' unused' /\
    LENGTH raw_slots' = LENGTH sites' /\
    PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0) /\
    (!a e cid ix h b0 done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret) ==>
      ?ret'. FLOOKUP calls' (a,e,cid) =
        SOME (ix,h,b0,done_at_call,child_entry,ret') /\
        (IS_SOME ret ==> ret' = ret))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)` >>
  `?sf inc entry order.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\ LAST order = d /\
    s.vs_inst_idx = LENGTH ps + n /\ n < LENGTH ys /\ inst = EL n ys` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `FLOOKUP acts p = _` mp_tac >>
     qpat_x_assum `LAST _ = d` mp_tac >>
     qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
     qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
     qpat_x_assum `case body_entry of NONE => _ | SOME v => _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  `SUC (LENGTH ps + n) < LENGTH bt.bb_instructions` by
    (irule venomExecPropsTheory.non_terminator_not_last >>
     simp[EL_APPEND2] >> metis_tac[]) >>
  `SUC n < LENGTH ys` by gvs[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (SUC n) ys)` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `SUC n < LENGTH ys` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomWfTheory.bb_well_formed_def] >>
     simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
       (qspec_then `LENGTH ps + n'` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `FOLDR (dft_exec_cons (N-d) C8) OK (TAKE (SUC n) ys) be =
    OK (post with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule dft_packet_ordinary_prefix_extend >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[TAKE_SUC_BY_TAKE, EVERY_SNOC] >> metis_tac[]) >>
  qabbrev_tac `t = post with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `work = if inst.inst_opcode = GAS then
    FMAP_MAP2 (\(ae,rows). MAP2 (\ss kk. MAP2 (\slot key.
      if key = (p,d,inst.inst_id) then SOME (HD s.vs_gas_readings) else slot) ss kk)
      rows (THE (FLOOKUP ks_tab ae))) ms_tab else ms_tab` >>
  qabbrev_tac `nextblocks = blocks |+ ((p,d),
    (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),SUC n,OK t,F,NONE))` >>
  qabbrev_tac `nextobs = trace_gas (TAKE (SUC j)
    (trace_blocks [] 0 N C8 root_tf root_entry))` >>
  `FDOM work = FDOM ms_tab /\
   (!ae old new. FLOOKUP ms_tab ae = SOME old /\ FLOOKUP work ae = SOME new ==>
     LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new)` by
    (Cases_on `inst.inst_opcode = GAS`
     >- (irule dft_packet_keymap_refines >> goal_assum (drule_at Any) >>
         simp[Abbr `work`] >> qexists_tac `HD s.vs_gas_readings` >> simp[]) >>
     simp[Abbr `work`] >> rpt strip_tac >> gvs[] >>
     irule EVERY2_refl >> simp[] >> rpt strip_tac >>
     irule EVERY2_refl >> simp[]) >>
  qabbrev_tac `newAM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP work (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a)))))))))` >>
  qexistsl_tac [`N`,`nextobs`,`acts`,`nextblocks`,`calls`,`work`,
    `es_tab`,`ks_tab`,`p`,`d`,`newAM []`,`sites`,`t.vs_gas_readings`] >>
  conj_tac >- simp[] >>
  reverse conj_tac
  >- (once_rewrite_tac [CONJ_ASSOC] >> reverse conj_tac
      >- (rpt gen_tac >> strip_tac >> qexists_tac `ret` >> simp[]) >>
      `unused = s.vs_gas_readings /\
       raw_slots = FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e))))
         (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))` by
        (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
         rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
         qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         qpat_x_assum `unused = _` mp_tac >> qpat_x_assum `raw_slots = _` mp_tac >>
         qpat_x_assum `AM = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
      Cases_on `inst.inst_opcode = GAS`
      >- (`s.vs_gas_readings = HD s.vs_gas_readings :: TL s.vs_gas_readings` by
            (simp[listTheory.CONS]) >>
          `t.vs_gas_readings = TL s.vs_gas_readings` by
            (drule_all dftBlockSimTheory.step_inst_ok_gas >>
             simp[Abbr `t`] >> strip_tac >> gvs[] >>
             Cases_on `s.vs_gas_readings` >> gvs[]) >>
          `LENGTH (newAM []) = LENGTH sites` by
            (irule (cj 1 dft_packet_keymap_gas_conservation) >>
             goal_assum (drule_at (Pat `dft_focus_packet_rel`)) >>
             simp[Abbr `work`,Abbr `newAM`] >>
             goal_assum (drule_at Any) >> simp[]) >>
          `PERM (MAP THE (FILTER IS_SOME (newAM [])) ++ TL s.vs_gas_readings)
            (MAP THE (FILTER IS_SOME raw_slots) ++ s.vs_gas_readings)` by
            (irule (cj 2 dft_packet_keymap_gas_conservation) >>
             goal_assum (drule_at (Pat `dft_focus_packet_rel`)) >>
             simp[Abbr `work`,Abbr `newAM`] >>
             goal_assum (drule_at Any) >> simp[]) >>
          simp[] >> metis_tac[sortingTheory.PERM_TRANS]) >>
      drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >>
      simp[Abbr `t`,Abbr `newAM`,Abbr `work`] >> metis_tac[]) >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  map_every (fn pat => qpat_x_assum pat (SUBST_ALL_TAC o SYM))
    [`j = _`,`obs = _`,`stk = _`,`PG = _`,`G = _`,`tn = _`,
     `fn = _`,`inst = _`,`s = _`,`oms = _`,`om = _`,`hs = _`,`h = _`] >>
  pure_rewrite_tac[dft_focus_packet_rel_def] >>
  qexistsl_tac [`SUC j`,`nextobs`,`newAM`,`AE`,`AK`,`row_eval`,`plan_eval`,
    `call_setup`,`plan_ok`,`levels_ok`,`stk`,`PG`,`step_prov PG G inst post`,
    `step_taint inst s post tn`,`fn`,`inst'`,`t`,`oms`,`origin_step PG om inst post`,
    `hs`,`h ++ [OriginOrdinary fuel post; OriginObserve
      (OriginSnapshot fn PG (step_prov PG G inst post) (origin_step PG om inst post) inst' t)]`] >>
  qpat_assum `q8' = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[REFL_CLAUSE,AND_CLAUSES] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`nm`,`lbl`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[NoAsms,Abbr `nextobs`] >>
  `nextobs = obs ++ (if inst.inst_opcode = GAS then
      [((p,d,inst.inst_id),HD s.vs_gas_readings)] else [])` by
    (simp[NoAsms,Abbr `nextobs`] >>
     map_every (fn pat => qpat_x_assum pat mp_tac)
       [`TAKE (SUC j) _ = _`,`obs = _`,`inst.inst_opcode = GAS ==> _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_assum `TAKE (SUC j) _ = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `obs = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms,dftGasFromListReadingsTheory.trace_gas_append,
       dftGasFromListReadingsTheory.trace_gas_cons,
       dftGasFromListReadingsTheory.trace_gas_nil,visit_gas_def] >>
     Cases_on `inst.inst_opcode = GAS` >> simp[NoAsms] >>
     Cases_on `s.vs_gas_readings` >> gvs[]) >>
  `root_entry.vs_gas_readings = MAP SND nextobs ++ t.vs_gas_readings` by
    (simp[NoAsms,Abbr `t`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`root_entry.vs_gas_readings = _`,`nextobs = obs ++ _`,
        `inst.inst_opcode = GAS ==> _`,`inst.inst_opcode <> INVOKE`,
        `step_inst fuel C8 inst s = OK post`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_assum `nextobs = obs ++ _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `inst.inst_opcode = GAS`
     >- (drule_all dftBlockSimTheory.step_inst_ok_gas >>
         strip_tac >> Cases_on `s.vs_gas_readings` >>
         gvs[venomStateTheory.update_var_def]) >>
     drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >>
     simp[]) >>
  conj_tac >- (qpat_assum `root_entry.vs_gas_readings = _` SUBST1_TAC >> simp[]) >>
  conj_tac >- simp[NoAsms,Abbr `newAM`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[NoAsms,Abbr `nextobs`] >>
      irule dftGasFromListTraceNamesTheory.trace_gas_names_distinct >>
      pure_rewrite_tac[MAP_TAKE] >>
      irule listTheory.ALL_DISTINCT_TAKE >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `LENGTH (newAM []) = LENGTH (AE []) /\
   LENGTH (newAM []) = LENGTH (AK []) /\
   PERM (MAP (\(key,slot). (key,THE slot))
     (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],newAM [])))) nextobs` by
    (Cases_on `inst.inst_opcode = GAS`
     >- (`s.vs_gas_readings = HD s.vs_gas_readings :: TL s.vs_gas_readings` by
           simp[listTheory.CONS] >>
         `LENGTH (newAM []) = LENGTH sites /\
          PERM (MAP THE (FILTER IS_SOME (newAM [])) ++ TL s.vs_gas_readings)
            (MAP THE (FILTER IS_SOME raw_slots) ++ s.vs_gas_readings) /\
          PERM (MAP (\(key,slot). (key,THE slot))
            (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],newAM []))))
            (obs ++ [((p,d,inst.inst_id),HD s.vs_gas_readings)])` by
           (map_every (fn pat => qpat_assum pat mp_tac)
              [`dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
               `FLOOKUP blocks (p,d) = SOME
                 (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
               `AM = _`,`AK = _`,`Abbrev (work = _)`,`Abbrev (newAM = _)`,
               `inst.inst_opcode = GAS`,
               `s.vs_gas_readings = HD s.vs_gas_readings :: TL s.vs_gas_readings`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
            irule dft_packet_keymap_gas_conservation >>
            conj_tac >- first_assum ACCEPT_TAC >>
            conj_tac >- first_assum ACCEPT_TAC >>
            goal_assum (drule_at (Pat `dft_focus_packet_rel`)) >>
            simp[Abbr `work`,Abbr `newAM`] >>
            goal_assum (drule_at Any) >> simp[]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`LENGTH (newAM []) = LENGTH sites`,`sites = AE []`,
            `LENGTH (AM []) = LENGTH (AE [])`,`LENGTH (AM []) = LENGTH (AK [])`,
            `PERM _ (obs ++ [((p,d,inst.inst_id),HD s.vs_gas_readings)])`,
            `nextobs = obs ++ _`,`inst.inst_opcode = GAS`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
     `newAM = AM` by
       (simp[NoAsms,Abbr `newAM`] >>
        qpat_assum `AM = _` (fn th => pure_rewrite_tac[th]) >>
        simp[Abbr `work`]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`newAM = AM`,`nextobs = obs ++ _`,`inst.inst_opcode <> GAS`,
        `LENGTH (AM []) = LENGTH (AE [])`,`LENGTH (AM []) = LENGTH (AK [])`,
        `PERM _ obs`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[NoAsms,Abbr `nextblocks`] >>
      qpat_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
      qpat_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
      qpat_assum `FDOM work = FDOM ms_tab` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      gvs[FLOOKUP_DEF] >> ASM_SET_TAC[]) >>
  `FDOM nextblocks = FDOM blocks` by
    (simp[NoAsms,Abbr `nextblocks`] >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     gvs[FLOOKUP_DEF] >> ASM_SET_TAC[]) >>
  qpat_assum `FDOM nextblocks = FDOM blocks`
    (fn th => pure_rewrite_tac[th]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `order'` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
            FLOOKUP blocks (a,e) = _ ==> _`,
         `FLOOKUP blocks (p,d) = SOME
            (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
         `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
         `LAST order = d`,`SUC n < LENGTH ys`,
         `inst = EL n ys`,`~is_terminator inst.inst_opcode`,
         `inst.inst_opcode <> INVOKE`,`step_inst fuel C8 inst s = OK post`,
         `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (SUC n) ys)`,
         `Abbrev (t = _)`,`Abbrev (nextblocks = _)`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _` (mk_asm "old_blocks") >>
      rpt gen_tac >> strip_tac >>
      rename1 `FLOOKUP nextblocks (a,e) = SOME
        (bba,bta,psa,xsa,ysa,rhoa,ina,ha,bea,ca,ra,closa,rsta)` >>
      Cases_on `(a,e) = (p,d)`
      >- (qpat_x_assum `FLOOKUP nextblocks (a,e) = _` mp_tac >>
          simp[Abbr `nextblocks`,FLOOKUP_UPDATE] >> strip_tac >>
          gvs[] >> asm_x "old_blocks" drule >> strip_tac >>
          qpat_x_assum `FLOOKUP acts a = SOME _` mp_tac >>
          qpat_assum `FLOOKUP acts a = SOME _`
            (fn th => pure_rewrite_tac[th,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
          strip_tac >>
          map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
            [`sf = sf'`,`fn = tf`,`inc = inc'`,`entry = entry'`,
             `order = order'`] >>
          map_every (fn pat => qpat_x_assum pat (SUBST_ALL_TAC o SYM))
            [`NONE = res`,`NONE = nrest`] >>
          qpat_x_assum `case SOME (be,hbe) of NONE => _ | SOME _ => _`
            (strip_assume_tac o SIMP_RULE pure_ss
              [optionTheory.option_case_def,pairTheory.pair_case_thm]) >>
          qexists_tac `sp` >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          conj_tac >- decide_tac >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          conj_tac
          >- (Cases_on `LAST order' = SUC inc'`
              >- (qpat_x_assum `if LAST order' = SUC inc' then _ else _` mp_tac >>
                  simp[]) >>
              qpat_assum `LAST order' <> SUC inc'`
                (fn th => qpat_x_assum `if LAST order' = SUC inc' then _ else _`
                  (mp_tac o PURE_REWRITE_RULE [th,COND_CLAUSES])) >>
              strip_tac >>
              `LAST order' <> LAST order' - 1` by
                (strip_tac >>
                 qpat_x_assum `FLOOKUP blocks (a,LAST order') = _` mp_tac >>
                 qpat_assum `LAST order' = LAST order' - 1`
                   (fn th => pure_once_rewrite_tac[th]) >>
                 qpat_assum `FLOOKUP blocks (a,LAST order' - 1) = _`
                   (fn th => pure_rewrite_tac[th,optionTheory.SOME_11,
                     pairTheory.PAIR_EQ]) >> simp[NoAsms]) >>
              simp[] >> goal_assum (drule_at Any) >> simp[]) >>
          conj_tac >- decide_tac >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          rpt strip_tac >>
          simp[NoAsms,Abbr `t`] >>
          irule dft_packet_ordinary_prefix_extend >>
          conj_tac >- decide_tac >>
          conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
          conj_tac
          >- (qexistsl_tac [`fuel`,`EL n ys`] >>
              simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
          qpat_x_assum `EVERY _ (TAKE (SUC n) ys)` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> strip_tac >>
          drule rich_listTheory.EVERY_TAKE >>
          disch_then (qspec_then `n` mp_tac) >> simp[rich_listTheory.TAKE_TAKE_T]) >>
      `FLOOKUP blocks (a,e) =
        SOME (bba,bta,psa,xsa,ysa,rhoa,ina,ha,bea,ca,ra,closa,rsta)` by
        (qpat_x_assum `FLOOKUP nextblocks (a,e) = _` mp_tac >>
         simp[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
      asm_x "old_blocks" drule >> strip_tac >>
      qexistsl_tac [`sf'`,`tf`,`inc'`,`entry'`,`order'`,`res`,`nrest`,`sp`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- decide_tac >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (Cases_on `e = SUC inc'`
          >- (qpat_x_assum `if e = SUC inc' then _ else _` mp_tac >> simp[]) >>
          qpat_assum `e <> SUC inc'`
            (fn th => qpat_x_assum `if e = SUC inc' then _ else _`
              (mp_tac o PURE_REWRITE_RULE [th,COND_CLAUSES])) >>
          strip_tac >>
          `(a,e-1) <> (p,d)` by
            (strip_tac >>
             qpat_x_assum `FLOOKUP blocks (a,e-1) = _` mp_tac >>
             qpat_assum `(a,e-1) = (p,d)`
               (fn th => pure_once_rewrite_tac[th]) >>
             qpat_assum `FLOOKUP blocks (p,d) = _`
               (fn th => pure_rewrite_tac[th,optionTheory.SOME_11,
                 pairTheory.PAIR_EQ]) >> simp[NoAsms]) >>
          simp[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
          goal_assum (drule_at Any) >> simp[]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (Cases_on `bea`
          >- (qpat_x_assum `case NONE of NONE => _ | SOME _ => _` mp_tac >>
              simp[NoAsms] >> strip_tac >> gvs[]) >>
          PairCases_on `x` >>
          qpat_x_assum `case SOME _ of NONE => _ | SOME _ => _`
            (strip_assume_tac o SIMP_RULE pure_ss
              [optionTheory.option_case_def,pairTheory.pair_case_thm]) >>
          simp[NoAsms] >>
          conj_tac >- decide_tac >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          first_assum ACCEPT_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qexistsl_tac [`sf`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,
        `sched`,`in_state`,`h0`,`SOME (be,hbe)`,`SUC n`] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bt` by
        (qpat_x_assum `FLOOKUP blocks (p,d) = SOME
          (bb',bt',ps',xs',ys',rho',in_state',h0',body_entry,count',OK s,F,NONE)` mp_tac >>
         qpat_assum `FLOOKUP blocks (p,d) = SOME
          (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`
           (fn th => pure_rewrite_tac[th,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
         strip_tac >> qpat_x_assum `bt = bt'` SUBST1_TAC >>
         first_assum ACCEPT_TAC) >>
      `post.vs_current_bb = s.vs_current_bb` by
        (irule (cj 1 venomInstPropsTheory.step_preserves_control_flow) >>
         qexistsl_tac [`C8`,`fuel`,`inst`] >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      `t.vs_inst_idx = LENGTH ps + SUC n /\
       t.vs_current_bb = s.vs_current_bb` by simp[Abbr `t`] >>
      simp[NoAsms,Abbr `nextblocks`,FLOOKUP_UPDATE] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (qpat_assum `t.vs_current_bb = s.vs_current_bb`
            (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (simp[venomInstTheory.get_instruction_def,EL_APPEND2]) >>
      simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`!a e cid q h b0 done_at_call child_entry ret.
            FLOOKUP calls (a,e,cid) = _ ==> _`,
         `FLOOKUP blocks (p,d) = SOME
            (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
         `Abbrev (nextblocks = _)`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      map_every qx_gen_tac [`a`,`e`,`cid`,`q`,`call_h`,`b0`,`done_at_call`,`child_entry`,`ret`] >>
      strip_tac >>
      qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
        FLOOKUP calls (a,e,cid) = _ ==> _` drule >> strip_tac >>
      `?count1 front1 closed1 brest1.
        FLOOKUP nextblocks (a,e) = SOME
          (bb',bt',ps',xs',ys',rho',in_state',h0',SOME (be',hbe'),
           count1,front1,closed1,brest1) /\
        (!r. MEM r (TAKE count' rho') ==> MEM r (TAKE count1 rho'))` by
        (Cases_on `(a,e) = (p,d)`
         >- (gvs[] >>
             qexistsl_tac [`SUC count'`,`OK t`,`F`,`NONE`] >>
             simp[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
             simp[rich_listTheory.TAKE_SUC]) >>
         qexistsl_tac [`count'`,`front`,`closed`,`brest`] >>
         simp[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
      qexistsl_tac [`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,
        `bb'`,`bt'`,`ps'`,`xs'`,`ys'`,`rho'`,`in_state'`,`h0'`,`be'`,`hbe'`,
        `count1`,`front1`,`closed1`,`brest1`,`csf`,`ctf`,`child_order`,
        `child_res`,`child_rest`,`c`,`nm`,`ops`,`args`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- decide_tac >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      Cases_on `ret` >> gvs[] >> PairCases_on `x` >> gvs[]) >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`!k. k < LENGTH p ==>
           ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
             q h b0 done_at_call child_entry cid e a.
             a = DROP (SUC k) p /\ _`,
         `Abbrev (nextblocks = _)`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qx_gen_tac `k` >> strip_tac >>
      qpat_x_assum `!k. k < LENGTH p ==> _` drule >> strip_tac >>
      `(a,e) <> (p,d)` by
        (simp[] >> strip_tac >>
         qpat_x_assum `DROP (SUC k) p = p`
           (mp_tac o AP_TERM ``LENGTH : (num # num) list -> num``) >>
         pure_rewrite_tac [LENGTH_DROP] >> decide_tac) >>
      qexistsl_tac [`sf`,`tf`,`inc`,`entry`,`order`,`bb'`,`bt'`,`ps'`,`xs'`,`ys'`,`rho'`,
        `in_state'`,`h0'`,`be'`,`hbe'`,`count'`,`q`,`h`,`b0`,`done_at_call`,
        `child_entry`,`cid`,`e`,`a`] >>
      simp[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac
        [`a`,`e`,`rb`,`rt`,`rps`,`rxs`,`rys`,`rsched`,`rin`,`rh0`,`rbe`,`rhbe`,
         `rcount`,`rfront`,`rclosed`,`rrest`,`ms`,`ess`,`ks`] >>
      strip_tac >>
      `?oldms. FLOOKUP ms_tab (a,e) = SOME oldms /\
        LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldms ms` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`FDOM work = FDOM ms_tab`,`FLOOKUP work (a,e) = SOME ms`,
            `!ae old new. FLOOKUP ms_tab ae = SOME old /\ _ ==> _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         `(a,e) IN FDOM ms_tab` by metis_tac[finite_mapTheory.flookup_thm] >>
         `?oldms. FLOOKUP ms_tab (a,e) = SOME oldms` by
           metis_tac[venomExecProofsTheory.FDOM_FLOOKUP] >>
         qexists_tac `oldms` >> simp[] >> metis_tac[]) >>
      `!q. (EL q xs).inst_opcode = INVOKE ==>
        (MEM q (TAKE (SUC n) sched) <=> MEM q (TAKE n sched))` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
              FLOOKUP blocks (a,e) = _ ==> _`,
           `FLOOKUP blocks (p,d) = SOME
             (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
           `n < LENGTH ys`,`inst = EL n ys`,`inst.inst_opcode <> INVOKE`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
           FLOOKUP blocks (a,e) = _ ==> _` drule >> strip_tac >>
         `n < LENGTH sched /\ from_block [EL (EL n sched) xs] (EL n ys)` by
           (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
         `(EL (EL n sched) xs).inst_opcode <> INVOKE` by
           (strip_tac >> qpat_x_assum `from_block _ _` mp_tac >>
            simp[dftStructuralTheory.from_block_def,dftDefsTheory.is_flippable_def,
              venomEffectsTheory.is_commutative_def,passSharedDefsTheory.is_comparator_def,
              venomInstTheory.is_pseudo_def] >> metis_tac[]) >>
         metis_tac[dft_packet_ordinary_invoke_members]) >>
      `?oc ofront oclosed orest.
        FLOOKUP blocks (a,e) = SOME
          (rb,rt,rps,rxs,rys,rsched,rin,rh0,SOME (rbe,rhbe),oc,ofront,oclosed,orest) /\
        (!q. (EL q rxs).inst_opcode = INVOKE ==>
          (MEM q (TAKE rcount rsched) <=> MEM q (TAKE oc rsched)))` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP nextblocks (a,e) = _`,`Abbrev (nextblocks = _)`,
           `FLOOKUP blocks (p,d) = SOME
             (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
           `!q. (EL q xs).inst_opcode = INVOKE ==> _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         Cases_on `(a,e) = (p,d)`
         >- (gvs[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
             qexistsl_tac [`n`,`OK s`,`F`,`NONE`] >> simp[]) >>
         gvs[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
         qexistsl_tac [`rcount`,`rfront`,`rclosed`,`rrest`] >> simp[]) >>
      qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        FLOOKUP blocks (a,e) = _ /\ _ ==> _` drule_all >> strip_tac >>
      `LENGTH ms = LENGTH oldms /\
       LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
       LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldms ms`,
           `LIST_REL (\m es. LENGTH m = LENGTH es) oldms ess`,
           `LIST_REL (\m keys. LENGTH m = LENGTH keys) oldms ks`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
      ntac 3 (conj_tac >- simp[]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`rsf`,`rtf`,`rinc`,`rentry`,`rorder`,`rres`,`rnrest`] >>
      strip_tac >>
      qpat_x_assum `!sf tf inc entry order res nrest.
        FLOOKUP acts a = _ ==> _` drule >> strip_tac >>
      reverse conj_tac
      >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`!F k kgss tail. N <= F /\ _ ==> _`,
            `!q. (EL q rxs).inst_opcode = INVOKE ==> _`,
            `LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldms ms`] >>
          POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
          rpt gen_tac >> strip_tac >>
          `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
             (TAKE k oldms) kgss` by
            metis_tac[dftPacketRefinementBoundaryTheory.dft_packet_refined_take_compatible] >>
          `!q. q < k /\ (EL q rxs).inst_opcode = INVOKE ==>
            MEM q (TAKE oc rsched)` by metis_tac[] >>
          qpat_x_assum `!F k kgss tail. N <= F /\ _ ==> _` irule >> simp[]) >>
      `ms = if inst.inst_opcode = GAS then
        MAP2 (\ss kk. MAP2 (\slot key.
          if key = (p,d,inst.inst_id) then SOME (HD s.vs_gas_readings) else slot) ss kk)
          oldms ks else oldms` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`Abbrev (work = _)`,`FLOOKUP work (a,e) = SOME ms`,
           `FLOOKUP ms_tab (a,e) = SOME oldms`,`FLOOKUP ks_tab (a,e) = SOME ks`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         Cases_on `inst.inst_opcode = GAS` >>
         gvs[Abbr `work`,finite_mapTheory.FLOOKUP_FMAP_MAP2]) >>
      `!ca csf ctf cinc cent corder cres crest.
        FLOOKUP acts ca = SOME (csf,ctf,cinc,cent,corder,cres,crest) ==>
        newAM ca = if inst.inst_opcode = GAS then
          MAP2 (\slot key. if key = (p,d,inst.inst_id) then
            SOME (HD s.vs_gas_readings) else slot) (AM ca) (AK ca)
          else AM ca` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
           `Abbrev (work = _)`,`Abbrev (newAM = _)`,`AM = _`,`AK = _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> rpt gen_tac >> strip_tac >>
         Cases_on `inst.inst_opcode = GAS`
         >- (simp[Abbr `newAM`] >> irule dft_packet_keymap_activation >>
             simp[Abbr `work`] >> metis_tac[]) >>
         simp[Abbr `work`,Abbr `newAM`]) >>
      `~MEM (p,d,inst.inst_id) (MAP FST obs)` by
        (irule dft_packet_gas_fresh >> goal_assum (drule_at Any)) >>
      `!ca ce cid cv. FLOOKUP calls (ca,ce,cid) = SOME cv ==>
        ?csf ctf cent corder cres crest.
          FLOOKUP acts ((ce,cid)::ca) = SOME (csf,ctf,ce,cent,corder,cres,crest)` by
        (qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
           FLOOKUP calls (a,e,cid) = _ ==> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> disch_tac >> rpt gen_tac >>
         PairCases_on `cv` >> strip_tac >>
         qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. _` drule >>
         strip_tac >> goal_assum (drule_at Any)) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`ms = if _ then _ else _`,`nextobs = obs ++ _`,
         `~MEM (p,d,inst.inst_id) (MAP FST obs)`,
         `LENGTH oldms = LENGTH rxs`,`LENGTH ks = LENGTH oldms`,
         `!ca csf ctf cinc cent corder cres crest. _`,
         `!ca ce cid cv. _`, `!q. q < LENGTH rxs ==> _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qx_gen_tac `q` >> strip_tac >>
      qpat_x_assum `!q. q < LENGTH rxs ==> _` drule >> strip_tac >>
      Cases_on `inst.inst_opcode = GAS` >>
      simp[EL_MAP2,dft_packet_fresh_alookup] >> strip_tac >>
      Cases_on `FLOOKUP calls (a,e,(EL q rxs).inst_id)` >> gvs[] >>
      `?csf ctf cent corder cres crest.
        FLOOKUP acts ((e,(EL q rxs).inst_id)::a) =
          SOME (csf,ctf,e,cent,corder,cres,crest)` by metis_tac[] >>
      qpat_x_assum `!ca csf ctf cinc cent corder cres crest. _` drule >>
      simp[]) >>
  conj_tac
  >- (map_every qx_gen_tac
        [`a`,`e`,`cid`,`q`,`call_h`,`b0`,`done`,`child_entry`,`ret`,
         `rb`,`rt`,`rps`,`rxs`,`rys`,`rsched`,`rin`,`rh0`,`rbe`,`rhbe`,
         `rcount`,`rfront`,`rclosed`,`rrest`,`ms`] >> strip_tac >>
      `?oc ofront oclosed orest. FLOOKUP blocks (a,e) = SOME
        (rb,rt,rps,rxs,rys,rsched,rin,rh0,SOME (rbe,rhbe),oc,ofront,oclosed,orest)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP nextblocks (a,e) = _`,`Abbrev (nextblocks = _)`,
           `FLOOKUP blocks (p,d) = SOME
             (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         Cases_on `(a,e) = (p,d)` >> gvs[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
         goal_assum (drule_at Any)) >>
      `?oldms. FLOOKUP ms_tab (a,e) = SOME oldms /\
        LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldms ms` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`FDOM work = FDOM ms_tab`,`FLOOKUP work (a,e) = SOME ms`,
            `!ae old new. FLOOKUP ms_tab ae = SOME old /\ _ ==> _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         `(a,e) IN FDOM ms_tab` by metis_tac[finite_mapTheory.flookup_thm] >>
         `?oldms. FLOOKUP ms_tab (a,e) = SOME oldms` by
           metis_tac[venomExecProofsTheory.FDOM_FLOOKUP] >>
         qexists_tac `oldms` >> simp[] >> metis_tac[]) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`!a e cid q h b0 done_at_call child_entry ret
           bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
           FLOOKUP calls (a,e,cid) = _ /\ _ ==> _`,
         `FLOOKUP calls (a,e,cid) = _`,
         `FLOOKUP blocks (a,e) = SOME
           (rb,rt,rps,rxs,rys,rsched,rin,rh0,SOME (rbe,rhbe),oc,ofront,oclosed,orest)`,
         `FLOOKUP ms_tab (a,e) = SOME oldms`,
         `LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldms ms`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret
        bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms. _`
        drule >> simp[] >> disch_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`!F kgss tail u. N <= F /\ _ ==> _`,
         `LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldms ms`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> rpt gen_tac >> strip_tac >>
      `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE q oldms) kgss` by
        metis_tac[dftPacketRefinementBoundaryTheory.dft_packet_refined_take_compatible] >>
      qpat_x_assum `!F kgss tail u. N <= F /\ _ ==> _` irule >> metis_tac[]) >>
  `!a e rb rt rps rxs rys rho rin rh0 rentry rc rf rr.
    FLOOKUP blocks (a,e) = SOME
      (rb,rt,rps,rxs,rys,rho,rin,rh0,rentry,rc,rf,T,rr) ==>
    FLOOKUP work (a,e) = FLOOKUP ms_tab (a,e)` by
    (rpt gen_tac >> strip_tac >> Cases_on `inst.inst_opcode = GAS`
     >- (irule dft_packet_closed_keymap_row >>
         goal_assum (drule_at (Pat `dft_focus_packet_rel`)) >>
         simp[Abbr `work`] >>
         qexistsl_tac [`inst.inst_id`,`HD s.vs_gas_readings`] >> simp[]) >>
     simp[Abbr `work`]) >>
  conj_tac
  >- (map_every qx_gen_tac
        [`a`,`e`,`rsf`,`rtf`,`rinc`,`rent`,`rorder`,`rres`,`rrest`,
         `rb`,`rt`,`rps`,`rxs`,`rys`,`rsched`,`rin`,`rh0`,`rbe`,`rhbe`,
         `rcount`,`r8`,`u0`,`ms`,`ess`,`ks`] >> strip_tac >>
      `FLOOKUP blocks (a,e) = SOME
        (rb,rt,rps,rxs,rys,rsched,rin,rh0,SOME (rbe,rhbe),rcount,r8,T,SOME u0)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP nextblocks (a,e) = _`,`Abbrev (nextblocks = _)`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         Cases_on `(p,d) = (a,e)` >> gvs[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
      `FLOOKUP ms_tab (a,e) = SOME ms` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`!a e rb rt rps rxs rys rho rin rh0 rentry rc rf rr. _`,
           `FLOOKUP blocks (a,e) = _`,`FLOOKUP work (a,e) = SOME ms`] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`!a e sf tf inc entry order res nrest bb bt ps xs ys rho
            in_state h0 be hbe count r8 u0 ms ess ks.
           FLOOKUP acts a = _ /\ _ ==> _`,
         `FLOOKUP acts a = SOME (rsf,rtf,rinc,rent,rorder,rres,rrest)`,
         `FLOOKUP blocks (a,e) = SOME
           (rb,rt,rps,rxs,rys,rsched,rin,rh0,SOME (rbe,rhbe),rcount,r8,T,SOME u0)`,
         `FLOOKUP ms_tab (a,e) = SOME ms`,
         `FLOOKUP es_tab (a,e) = SOME ess`,`FLOOKUP ks_tab (a,e) = SOME ks`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho
        in_state h0 be hbe count r8 u0 ms ess ks. _` drule_all >> simp[]) >>
  `!a rsf rtf rinc rent rorder r8 rest.
    FLOOKUP acts a = SOME (rsf,rtf,rinc,rent,rorder,SOME r8,SOME rest) ==>
    newAM a = AM a` by
    (rpt gen_tac >> strip_tac >>
     `FLAT (MAP (\e. FLAT (THE (FLOOKUP work (a,e)))) rorder) =
      FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) rorder)` by
       (Cases_on `inst.inst_opcode = GAS`
        >- (irule (cj 2 dft_packet_closed_keymap_unchanged) >>
            goal_assum (drule_at (Pat `dft_focus_packet_rel`)) >>
            simp[Abbr `work`] >>
            qexistsl_tac [`inst.inst_id`,`HD s.vs_gas_readings`] >> simp[]) >>
        simp[Abbr `work`]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (newAM = _)`,`AM = _`,`FLOOKUP acts a = _`,
        `FLAT (MAP _ rorder) = FLAT (MAP _ rorder)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`!a sf tf inc entry order r8 u0. FLOOKUP acts a = _ ==> terminates r8 /\ _`,
         `!a rsf rtf rinc rent rorder r8 rest. _ ==> newAM a = AM a`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      map_every qx_gen_tac [`a`,`rsf`,`rtf`,`rinc`,`rent`,`rorder`,`r8`,`u0`] >>
      strip_tac >>
      `newAM a = AM a` by metis_tac[] >> asm_rewrite_tac[] >>
      qpat_x_assum `!a sf tf inc entry order r8 u0. _ ==> terminates r8 /\ _`
        drule >> simp[]) >>
  conj_tac
  >- (`!q. (EL q xs).inst_opcode = INVOKE ==>
        (MEM q (TAKE (SUC n) sched) <=> MEM q (TAKE n sched))` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
              FLOOKUP blocks (a,e) = _ ==> _`,
           `FLOOKUP blocks (p,d) = SOME
             (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
           `n < LENGTH ys`,`inst = EL n ys`,`inst.inst_opcode <> INVOKE`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
           FLOOKUP blocks (a,e) = _ ==> _` drule >> strip_tac >>
         `n < LENGTH sched /\ from_block [EL (EL n sched) xs] (EL n ys)` by
           (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
         `(EL (EL n sched) xs).inst_opcode <> INVOKE` by
           (strip_tac >> qpat_x_assum `from_block _ _` mp_tac >>
            simp[dftStructuralTheory.from_block_def,dftDefsTheory.is_flippable_def,
              venomEffectsTheory.is_commutative_def,passSharedDefsTheory.is_comparator_def,
              venomInstTheory.is_pseudo_def] >> metis_tac[]) >>
         metis_tac[dft_packet_ordinary_invoke_members]) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
           FLOOKUP blocks (a,e) = _ ==> !q. _`,
         `FLOOKUP blocks (p,d) = SOME
           (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
         `Abbrev (nextblocks = _)`,`!q. (EL q xs).inst_opcode = INVOKE ==> _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      map_every qx_gen_tac
        [`a`,`e`,`rb`,`rt`,`rps`,`rxs`,`rys`,`rsched`,`rin`,`rh0`,
         `rbe`,`rhbe`,`rcount`,`rfront`,`rclosed`,`rrest`] >> strip_tac >>
      Cases_on `(a,e) = (p,d)` >> gvs[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac
        [`rb`,`rt`,`rps`,`rxs`,`rys`,`rsched`,`rin`,`rh0`,`rbe`,`rhbe`,
         `rcount`,`rsf`,`rinc`,`rent`,`rorder`] >> strip_tac >>
      `rb = bb /\ rt = bt /\ rps = ps /\ rxs = xs /\ rys = ys /\
       rsched = sched /\ rcount = SUC n /\ rsf = sf` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP nextblocks (p,d) = _`,`Abbrev (nextblocks = _)`,
           `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
           `FLOOKUP acts p = SOME (rsf,fn,rinc,rent,rorder,NONE,NONE)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,FLOOKUP_UPDATE]) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`rb = bb`,`rt = bt`,`rps = ps`,`rxs = xs`,`rys = ys`,
         `rsched = sched`,`rcount = SUC n`,`rsf = sf`,
         `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
           FLOOKUP blocks (a,e) = _ ==> _`,
         `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> MEM sf C7.ctx_functions /\ _`,
         `FLOOKUP blocks (p,d) = SOME
           (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
         `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
         `SUC n < LENGTH ys`,`inst' = EL (SUC n) ys`,
         `inv_memory_observation inst'.inst_opcode`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
        [`rb = bb`,`rt = bt`,`rps = ps`,`rxs = xs`,`rys = ys`,
         `rsched = sched`,`rcount = SUC n`,`rsf = sf`] >>
      qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
        drule >> strip_tac >>
      `from_block [EL (EL (SUC n) sched) xs] inst'` by
        (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
      `EL (EL (SUC n) sched) xs = inst'` by
        (drule_all dftGasInvMemoryObservationTheory.inv_memory_observation_original >> simp[]) >>
      conj_tac >- simp[] >>
      irule dft_packet_memory_schedule_predecessors >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `!a sf tf inc entry order res nrest.
        _ ==> MEM sf C7.ctx_functions /\ _` drule >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  map_every qx_gen_tac
    [`a`,`e`,`csf`,`ctf`,`cinc`,`cent`,`corder`,`cres`,`crest`,
     `cb`,`ct`,`cps`,`cxs`,`cys`,`crho`,`cin`,`ch0`,`cbody`,`ccount`,
     `cfront`,`cclosed`,`cbrest`,`q`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?oldcount oldfront.
    FLOOKUP blocks (a,e) = SOME
      (cb,ct,cps,cxs,cys,crho,cin,ch0,cbody,oldcount,oldfront,cclosed,cbrest) /\
    IS_SOME cbody /\ q < LENGTH cxs /\
    z = DROP (phi_prefix_length cb.bb_instructions) cps ++ TAKE q cxs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q cxs) /\
    (!r. r < q /\ (EL r cxs).inst_opcode = INVOKE ==>
      MEM r (TAKE oldcount crho))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP nextblocks (a,e) = _`,`Abbrev (nextblocks = _)`,
       `FLOOKUP blocks (p,d) = SOME
         (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`,
       `IS_SOME cbody /\ _ \/ _`,
       `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> _`,
       `n < LENGTH ys`,`inst = EL n ys`,`inst.inst_opcode <> INVOKE`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `(a,e) = (p,d)`
     >- (gvs[Abbr `nextblocks`,FLOOKUP_UPDATE] >>
         qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
           drule >> strip_tac >>
         `n < LENGTH crho /\ from_block [EL (EL n crho) cxs] (EL n cys)` by
           (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
         `(EL (EL n crho) cxs).inst_opcode <> INVOKE` by
           (strip_tac >> qpat_x_assum `from_block _ _` mp_tac >>
            simp[dftStructuralTheory.from_block_def,dftDefsTheory.is_flippable_def,
              venomEffectsTheory.is_commutative_def,passSharedDefsTheory.is_comparator_def,
              venomInstTheory.is_pseudo_def] >> metis_tac[]) >>
         metis_tac[dft_packet_ordinary_invoke_members]) >>
     `~(p = a /\ d = e)` by metis_tac[] >>
     `FLOOKUP blocks (a,e) = SOME
       (cb,ct,cps,cxs,cys,crho,cin,ch0,cbody,ccount,cfront,cclosed,cbrest)` by
       (Cases_on `p = a` >> Cases_on `d = e` >>
        gvs[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
     `IS_SOME cbody` by
       (qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
          drule >> strip_tac >> Cases_on `cbody` >> gvs[]) >>
     qexistsl_tac [`ccount`,`cfront`] >> simp[] >> metis_tac[]) >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
    body_entry count front closed brest q z. _`
    (drule_at (Pat `FLOOKUP blocks _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP acts _ = _`)) >>
  disch_then (qspecl_then [`q`,`z`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!ae. FST (THE (FLOOKUP nextblocks ae)) =
         FST (THE (FLOOKUP blocks ae))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`Abbrev (nextblocks = _)`,`FLOOKUP blocks (p,d) = SOME
        (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     gen_tac >> Cases_on `ae = (p,d)` >>
     gvs[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
  `!ai ds.
    MAP (\f. case THE (FLOOKUP nextblocks (ai,f)) of
      (bf,rest) => (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds =
    MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
      (bf,rest) => (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds` by
    (qpat_assum `!ae. FST (THE (FLOOKUP nextblocks ae)) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> disch_tac >>
     rpt gen_tac >> irule MAP_CONG >> simp[] >> gen_tac >> strip_tac >>
     first_x_assum (qspec_then `(ai,x)` mp_tac) >>
     Cases_on `THE (FLOOKUP nextblocks (ai,x))` >>
     Cases_on `THE (FLOOKUP blocks (ai,x))` >> simp[]) >>
  qabbrev_tac `newcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP work (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP work (ai,ei))))) cuts)` >>
  qexistsl_tac [`cuts`,`levels`,`newcut`,`Ecut`,`Kcut`,
    `DROP (LENGTH newcut) (newAM [])`,`er`,`kr`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`!i ai ds ei qi zi. _`,`!ai ds. MAP _ ds = _`,
         `Abbrev (nextblocks = _)`,`FLOOKUP blocks (p,d) = SOME
           (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      qpat_x_assum `!ai ds. MAP _ ds = _` (fn th => pure_rewrite_tac[th]) >>
      map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_x_assum `!i ai ds ei qi zi. _` drule_all >> strip_tac >>
      Cases_on `(ai,ei) = (p,d)`
      >- (gvs[Abbr `nextblocks`,FLOOKUP_UPDATE] >> metis_tac[]) >>
      `FLOOKUP nextblocks (ai,ei) = FLOOKUP blocks (ai,ei)` by
        (Cases_on `p = ai` >> Cases_on `d = ei` >>
         gvs[Abbr `nextblocks`,FLOOKUP_UPDATE]) >>
      qpat_x_assum `FLOOKUP nextblocks (ai,ei) = _` SUBST1_TAC >>
      metis_tac[]) >>
  `newcut = if inst.inst_opcode = GAS then
      MAP2 (\slot key. if key = (p,d,inst.inst_id) then
        SOME (HD s.vs_gas_readings) else slot) Mcut Kcut else Mcut` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`Abbrev (newcut = _)`,`Abbrev (work = _)`,`Mcut = _`,`Kcut = _`,
       `!i ai ds ei qi zi. _`,`dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `inst.inst_opcode = GAS`
     >- (simp[] >>
         simp[NoAsms,Abbr `newcut`] >>
         map_every (fn pat => qpat_x_assum pat (fn th => pure_rewrite_tac[th]))
           [`Mcut = _`,`Kcut = _`] >>
         irule (cj 1 dft_packet_flat_map2) >>
         gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
         `?i. i < LENGTH cuts /\ EL i cuts = (x0,x1,x2,x3,x4)` by
           metis_tac[MEM_EL] >>
         qpat_x_assum `!i ai ds ei qi zi. _` drule_all >> strip_tac >>
         match_mp_tac (PURE_REWRITE_RULE [LENGTH_APPEND] dft_packet_keymap_cut_piece) >>
         conj_tac >- simp[Abbr `work`] >>
         rpt strip_tac >>
         `MEM f orderi` by gvs[] >>
         drule_all dft_packet_activation_rows >>
         disch_then ACCEPT_TAC) >>
     gvs[Abbr `newcut`,Abbr `work`]) >>
  `newAM [] = if inst.inst_opcode = GAS then
      MAP2 (\slot key. if key = (p,d,inst.inst_id) then
        SOME (HD s.vs_gas_readings) else slot) (AM []) (AK []) else AM []` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
       `Abbrev (work = _)`,`Abbrev (newAM = _)`,`AM = _`,`AK = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `inst.inst_opcode = GAS`
     >- (simp[] >> (metis_tac[dft_packet_keymap_root])) >>
     simp[Abbr `work`,Abbr `newAM`]) >>
  `LENGTH newcut = LENGTH Mcut /\ newcut = TAKE (LENGTH Mcut) (newAM [])` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`newcut = if _ then _ else _`,`newAM [] = if _ then _ else _`,
       `AM [] = Mcut ++ mr`,`AK [] = Kcut ++ kr`,`LENGTH Mcut = LENGTH Kcut`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `inst.inst_opcode = GAS` >>
     gvs[MAP2_APPEND,dft_packet_aligned_map2_take,TAKE_APPEND] >>
     metis_tac[TAKE_LENGTH_ID]) >>
  conj_tac >- simp[NoAsms,Abbr `newcut`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`LENGTH newcut = LENGTH Mcut`,`newcut = TAKE (LENGTH Mcut) (newAM [])`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      metis_tac[TAKE_DROP]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`LENGTH newcut = LENGTH Mcut`,`LENGTH Mcut = LENGTH Ecut`] >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`LENGTH newcut = LENGTH Mcut`,`LENGTH Mcut = LENGTH Kcut`] >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `LIST_REL (\old new. old = NONE \/ old = new) (AM []) (newAM [])` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
       `AM = _`,`AK = _`,`newAM [] = if _ then _ else _`,
       `ALL_DISTINCT (AK [])`,`LENGTH (AM []) = LENGTH (AK [])`,
       `FLOOKUP blocks (p,d) = SOME
         (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `inst.inst_opcode = GAS`
     >- (drule_all dft_packet_current_gas_key >> strip_tac >>
         `newAM [] = LUPDATE (SOME (HD s.vs_gas_readings)) n' (AM [])` by
           metis_tac[dft_key_substitute_lupdate] >>
         qpat_x_assum `newAM [] = LUPDATE _ _ _` SUBST1_TAC >>
         simp[LIST_REL_EL_EQN,EL_LUPDATE] >> metis_tac[]) >>
     qpat_x_assum `newAM [] = if _ then _ else _` mp_tac >>
     qpat_assum `inst.inst_opcode <> GAS` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN]) >>
  `LIST_REL (\old new. old = NONE \/ old = new) Mcut newcut` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`LIST_REL (\old new. old = NONE \/ old = new) (AM []) (newAM [])`,
       `newcut = TAKE (LENGTH Mcut) (newAM [])`,`AM [] = Mcut ++ mr`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     drule EVERY2_TAKE >> disch_then (qspec_then `LENGTH Mcut` mp_tac) >>
     simp[TAKE_APPEND]) >>
  rpt gen_tac >> strip_tac >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`LIST_REL (\old new. old = NONE \/ old = new) Mcut newcut`,
       `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) newcut gs`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  qpat_x_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _` drule_all >>
  disch_then (qspec_then `tail` mp_tac) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `extra` >> first_assum ACCEPT_TAC) >>
  Cases_on `SND (rooted_eval F' C7 levels
    (root_entry with vs_gas_readings := gs ++ tail))`
  >- (qpat_x_assum `case _ of OK _ => _ | Halt _ => _ | Abort _ _ => _ | IntRet _ _ => _ | Error _ => _`
        mp_tac >> simp[NoAsms] >> strip_tac >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (qpat_assum `IS_SOME cbody` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> Cases_on `cbody` >> simp[]) >>
      strip_tac >>
      qpat_x_assum `a = p` SUBST_ALL_TAC >>
      qpat_x_assum `e = d` SUBST_ALL_TAC >>
      `cb = bb /\ ct = bt /\ cps = ps /\ cxs = xs /\ cys = ys /\
       crho = sched /\ cin = in_state /\ ch0 = h0 /\ cbody = SOME (be,hbe) /\
       oldcount = n /\ oldfront = OK s` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP blocks (p,d) = SOME
             (cb,ct,cps,cxs,cys,crho,cin,ch0,cbody,oldcount,oldfront,cclosed,cbrest)`,
           `FLOOKUP blocks (p,d) = SOME
             (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[]) >>
      map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
        [`cb = bb`,`ct = bt`,`cps = ps`,`cxs = xs`,`cys = ys`,
         `crho = sched`,`cin = in_state`,`ch0 = h0`,`cbody = SOME (be,hbe)`,
         `oldcount = n`,`oldfront = OK s`] >>
      `rooted_eval F' C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
        (Ecut,OK v)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`SND (rooted_eval _ _ _ _) = OK v`,`FST (rooted_eval _ _ _ _) = Ecut`] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[pairTheory.PAIR]) >>
      drule_at (Pat `FLOOKUP blocks _ = _`) dft_packet_cut_row_trace >>
      disch_then (drule_at (Pat `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `rooted_eval _ _ _ _ = _`)) >>
      disch_then (drule_at (Pat `FDOM _ = FDOM ms_tab`)) >>
      disch_then (qspecl_then [`q`,`z`,`cuts`,`newcut`] mp_tac) >>
      (impl_tac
       >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
           conj_tac
           >- (qpat_assum `!i ai ds ei qi zi. _` mp_tac >>
               POP_ASSUM_LIST (K all_tac) >>
               simp[pairTheory.pair_CASE_def]) >>
           simp[NoAsms,Abbr `newcut`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
           first_assum ACCEPT_TAC)) >>
      strip_tac >>
      `?rowms rowks newms rowes. FLOOKUP ms_tab (p,d) = SOME rowms /\
        FLOOKUP ks_tab (p,d) = SOME rowks /\ FLOOKUP work (p,d) = SOME newms /\
        FLOOKUP es_tab (p,d) = SOME rowes` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM ks_tab`,
           `FDOM blocks = FDOM es_tab`,`FDOM work = FDOM ms_tab`,
           `FLOOKUP blocks (p,d) = SOME
             (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
      `ALL_DISTINCT (FLAT rowks)` by
        (qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
           _ ==> _` (mp_tac o cj 6) >>
         disch_then (drule_at (Pat `FLOOKUP ks_tab _ = _`)) >>
         disch_then (drule_at (Pat `FLOOKUP ms_tab _ = _`)) >>
         disch_then (drule_at (Pat `FLOOKUP blocks _ = _`)) >>
         disch_then (drule_at (Pat `FLOOKUP es_tab _ = _`)) >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `LIST_REL (\key slot. slot = ALOOKUP nextobs key)
        (FLAT (TAKE q rowks)) (FLAT (TAKE q newms))` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
           `FLOOKUP ms_tab (p,d) = SOME rowms`,`FLOOKUP ks_tab (p,d) = SOME rowks`,
           `FLOOKUP work (p,d) = SOME newms`,`Abbrev (work = _)`,
           `nextobs = obs ++ _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         Cases_on `inst.inst_opcode = GAS`
         >- (drule dft_packet_gas_fresh >> disch_tac >>
             drule_all dft_packet_retained_fresh_lookup >>
             disch_then (qspecl_then [`HD s.vs_gas_readings`,`q`] mp_tac) >>
             gvs[Abbr `work`,FLOOKUP_FMAP_MAP2]) >>
         drule_all dft_packet_retained_prefix_lookup >>
         disch_then (qspec_then `q` mp_tac) >> gvs[Abbr `work`]) >>
      `ALL_DISTINCT (MAP FST nextobs)` by
        (simp[NoAsms,Abbr `nextobs`] >>
         irule dftGasFromListTraceNamesTheory.trace_gas_names_distinct >>
         pure_rewrite_tac[MAP_TAKE] >>
         irule listTheory.ALL_DISTINCT_TAKE >> first_assum ACCEPT_TAC) >>
      `ALL_DISTINCT (FLAT (TAKE q rowks))` by
        (qpat_assum `ALL_DISTINCT (FLAT rowks)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         `rowks = TAKE q rowks ++ DROP q rowks` by simp[TAKE_DROP] >>
         metis_tac[FLAT_APPEND,ALL_DISTINCT_APPEND]) >>
      `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
        (FLAT (TAKE q newms)) (FLAT kgss)` by
        (qpat_assum `LIST_REL (LIST_REL _) (TAKE q (THE (FLOOKUP work (p,d)))) kgss` mp_tac >>
         qpat_assum `FLOOKUP work (p,d) = SOME newms` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
         drule LIST_REL_LENGTH >> disch_tac >>
         drule dft_packet_flat_prefix_lookup >>
         disch_then (qspec_then `LENGTH kgss` mp_tac) >>
         simp[TAKE_LENGTH_TOO_LONG]) >>
      `EVERY (\kw. MEM kw nextobs)
        (trace_gas (trace_block p d (N-d) C8 fn
          (bt with bb_instructions := TAKE (LENGTH ps + SUC n) bt.bb_instructions) be))` by
        (simp[NoAsms,Abbr `nextobs`] >>
         drule_at (Pat `FLOOKUP blocks _ = _`) dft_packet_body_target_observations >>
         disch_then (drule_at (Pat `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
         disch_then (qspecl_then [`fuel`,`post`,`t`] mp_tac) >>
         simp[Abbr `t`]) >>
      `?orc.
        trace_agrees orc (trace_block p d (F'-d) C7
          (FST (THE (FLOOKUP acts p)))
          (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
          (be with vs_gas_readings := FLAT kgss ++ tail)) /\
        trace_agrees orc (trace_block p d (N-d) C8 fn
          (bt with bb_instructions := TAKE (LENGTH ps + SUC n) bt.bb_instructions) be)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`ALL_DISTINCT (MAP FST nextobs)`,`ALL_DISTINCT (FLAT (TAKE q rowks))`,
           `LIST_REL (\key slot. slot = ALOOKUP nextobs key) _ _`,
           `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q newms)) (FLAT kgss)`,
           `trace_gas (trace_block p d (F'-d) _ _ _ _) = _`,
           `FLOOKUP ks_tab (p,d) = SOME rowks`,
           `EVERY (\kw. MEM kw nextobs) _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         gvs[] >> drule_all dft_packet_common_oracle >>
         strip_tac >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
      qpat_assum `!F kgss tail q u orc.
        _ ==> (_ /\ u.vs_initial_fmp = t.vs_initial_fmp)` drule_all >>
      disch_then ACCEPT_TAC) >>
  qpat_x_assum `case _ of OK _ => _ | Halt _ => _ | Abort _ _ => _ | IntRet _ _ => _ | Error _ => _`
    mp_tac >> simp[NoAsms]
QED

(* A historical cut ending before the replaced segment stays a root prefix. *)
Theorem dft_packet_cut_prefix_frame[local]:
  !cut pre mid post mid' r.
    pre ++ mid ++ post = cut ++ r /\ LENGTH cut <= LENGTH pre ==>
    ?r'. pre ++ mid' ++ post = cut ++ r'
Proof
  rpt strip_tac >>
  `TAKE (LENGTH cut) (pre ++ mid' ++ post) = cut` by
    (qsuff_tac `TAKE (LENGTH cut) (pre ++ mid' ++ post) =
                 TAKE (LENGTH cut) (pre ++ mid ++ post)`
     >- (qpat_x_assum `pre ++ mid ++ post = _` SUBST1_TAC >>
         simp[TAKE_APPEND]) >>
     simp[GSYM APPEND_ASSOC,TAKE_APPEND1]) >>
  qexists_tac `DROP (LENGTH cut) (pre ++ mid' ++ post)` >>
  metis_tac[TAKE_DROP]
QED

Theorem dft_packet_cut_flat_frame[local]:
  !cuts tab tab'.
    (!ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) cuts ==>
      (!f. MEM f ds ==> FLOOKUP tab' (ai,f) = FLOOKUP tab (ai,f)) /\
      TAKE qi (THE (FLOOKUP tab' (ai,ei))) =
        TAKE qi (THE (FLOOKUP tab (ai,ei)))) ==>
    FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab' (ai,ei))))) cuts) =
    FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cuts)
Proof
  rpt strip_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
  gen_tac >> PairCases_on `x` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

(* Conditional transport only: concrete splices must establish every frame law.
   The semantic certificate still refers to the old cursor p,d,st,inst. *)
Theorem dft_packet_historical_cut_transport:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  a <> b /\
  Mroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Eroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Kroot = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) /\
  Mroot' = FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) /\
  Eroot' = FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) /\
  Kroot' = FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) /\
  (?hm vm wm vm'. Mroot = hm ++ vm ++ wm /\ Mroot' = hm ++ vm' ++ wm /\
    LENGTH Mcut <= LENGTH hm) /\
  (?he ve we ve'. Eroot = he ++ ve ++ we /\ Eroot' = he ++ ve' ++ we /\
    LENGTH Ecut <= LENGTH he) /\
  (?hk vk wk vk'. Kroot = hk ++ vk ++ wk /\ Kroot' = hk ++ vk' ++ wk /\
    LENGTH Kcut <= LENGTH hk) /\
  (!ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) cuts ==>
    FLOOKUP acts' ai = FLOOKUP acts ai /\
    FLOOKUP blocks' (ai,ei) = FLOOKUP blocks (ai,ei) /\
    (!cid. FLOOKUP calls' (ai,ei,cid) = FLOOKUP calls (ai,ei,cid)) /\
    (!f. MEM f ds ==>
      FST (THE (FLOOKUP blocks' (ai,f))) = FST (THE (FLOOKUP blocks (ai,f))) /\
      FLOOKUP ms_tab' (ai,f) = FLOOKUP ms_tab (ai,f) /\
      FLOOKUP es_tab' (ai,f) = FLOOKUP es_tab (ai,f) /\
      FLOOKUP ks_tab' (ai,f) = FLOOKUP ks_tab (ai,f)) /\
    TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))) = TAKE qi (THE (FLOOKUP ms_tab (ai,ei))) /\
    TAKE qi (THE (FLOOKUP es_tab' (ai,ei))) = TAKE qi (THE (FLOOKUP es_tab (ai,ei))) /\
    TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))) = TAKE qi (THE (FLOOKUP ks_tab (ai,ei)))) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
  Mroot = Mcut ++ mr /\ Eroot = Ecut ++ er /\ Kroot = Kcut ++ kr /\
  LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
    levels_ok F C7 levels
      (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
      (MAP (\(ai,ds,ei,qi,zi).
        FST (SND (SND (THE (FLOOKUP acts ai)))) ) cuts)
      root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. Ecut = FST (rooted_eval F C7 levels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
        u.vs_gas_readings = tail /\
        (?before after.
          dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((a,e,(EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
          dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
        (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
          (Ecut,OK (u with vs_gas_readings := tail'))) /\
        (body_entry = NONE ==> u with vs_gas_readings := st.vs_gas_readings = st) /\
        (a = p /\ e = d /\ IS_SOME body_entry /\
          inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
          (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op st) /\
          u.vs_initial_fmp = st.vs_initial_fmp)
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))) ==>
  ?mr' er' kr'.
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then
          ai = a /\ ei = e /\ qi = q /\ zi = z
         else
          ?cid h b0 done_at_call child_entry ret.
            EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
            FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
            qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
            zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
            EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
            (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
        EL i levels =
          (sfi, MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
            DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
              (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++
            [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
    Mroot' = Mcut ++ mr' /\ Eroot' = Ecut ++ er' /\ Kroot' = Kcut ++ kr' /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      levels_ok F C7 levels
        (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
        (MAP (\(ai,ds,ei,qi,zi).
          FST (SND (SND (THE (FLOOKUP acts' ai)))) ) cuts)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
              (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail'))) /\
          (body_entry = NONE ==> u with vs_gas_readings := st.vs_gas_readings = st) /\
          (a = p /\ e = d /\ IS_SOME body_entry /\
            inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op st) /\
            u.vs_initial_fmp = st.vs_initial_fmp)
      | stopped =>
          run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  strip_tac >>
  `?mr'. Mroot' = Mcut ++ mr'` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`Mroot = _ ++ _ ++ _`,`Mroot' = _ ++ _ ++ _`,
       `Mroot = Mcut ++ mr`,`LENGTH Mcut <= LENGTH hm`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[dft_packet_cut_prefix_frame]) >>
  `?er'. Eroot' = Ecut ++ er'` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`Eroot = _ ++ _ ++ _`,`Eroot' = _ ++ _ ++ _`,
       `Eroot = Ecut ++ er`,`LENGTH Ecut <= LENGTH he`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[dft_packet_cut_prefix_frame]) >>
  `?kr'. Kroot' = Kcut ++ kr'` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`Kroot = _ ++ _ ++ _`,`Kroot' = _ ++ _ ++ _`,
       `Kroot = Kcut ++ kr`,`LENGTH Kcut <= LENGTH hk`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[dft_packet_cut_prefix_frame]) >>
  qexistsl_tac [`mr'`,`er'`,`kr'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "description" >>
  conj_tac >- suspend "masks" >>
  conj_tac >- suspend "sites" >>
  conj_tac >- suspend "keys" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "semantics"
QED

Resume dft_packet_historical_cut_transport[description]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!ai ds ei qi zi. MEM _ cuts ==> _`,`!i ai ds ei qi zi. _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM (ai,ds,ei,qi,zi) cuts` by metis_tac[MEM_EL] >>
  qpat_x_assum `!ai ds ei qi zi. MEM _ cuts ==> _` drule >> strip_tac >>
  `MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
       (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds =
   MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
       (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds` by
    (irule MAP_CONG >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!i ai ds ei qi zi. _` drule_all >> simp[]
QED
Resume dft_packet_historical_cut_transport[masks]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!ai ds ei qi zi. MEM _ cuts ==> _`,`Mcut = FLAT _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `Mcut = _` SUBST1_TAC >> sym_tac >>
  irule dft_packet_cut_flat_frame >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED
Resume dft_packet_historical_cut_transport[sites]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!ai ds ei qi zi. MEM _ cuts ==> _`,`Ecut = FLAT _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `Ecut = _` SUBST1_TAC >> sym_tac >>
  irule dft_packet_cut_flat_frame >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED
Resume dft_packet_historical_cut_transport[keys]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!ai ds ei qi zi. MEM _ cuts ==> _`,`Kcut = FLAT _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `Kcut = _` SUBST1_TAC >> sym_tac >>
  irule dft_packet_cut_flat_frame >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED
Resume dft_packet_historical_cut_transport[semantics]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!ai ds ei qi zi. MEM _ cuts ==> _`,
     `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  `MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts =
   MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts` by
    (irule MAP_CONG >> simp[] >> gen_tac >> PairCases_on `x` >> simp[] >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  asm_rewrite_tac[]
QED
Finalise dft_packet_historical_cut_transport

Theorem dft_focus_packet_return_successor:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h)
    raw_slots sites unused /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  (rinst.inst_opcode = GAS ==> s.vs_gas_readings <> []) /\
  active_inst fn rinst s /\ step_inst fuel C8 rinst s = IntRet ret s_end /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
  active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?N' obs' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d' raw_slots' sites' unused'.
    N <= N' /\
    dft_focus_packet_rel N' C7 C8 root_sf root_tf root_entry
      (SUC (FST packet),obs')
      acts' blocks' calls' ms_tab' es_tab' ks_tab' rooted_eval p' d'
      (JointConfig stk f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
        (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs
        (caller_h ++ [OriginResume fuel fn rinst s ret s_end s'; OriginObserve
          (OriginSnapshot f.cf_fn f.cf_params
            (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
            (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) inst'
            (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))]))
      raw_slots' sites' unused' /\
    LENGTH raw_slots' = LENGTH sites' /\
    PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0) /\
    (!a e cid ix h b0 done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret) ==>
      ?ret'. FLOOKUP calls' (a,e,cid) =
        SOME (ix,h,b0,done_at_call,child_entry,ret') /\
        (IS_SOME ret ==> ret' = ret))
Proof
  strip_tac >>
  qabbrev_tac `dst = JointConfig stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
    (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs
    (caller_h ++ [OriginResume fuel fn rinst s ret s_end s'; OriginObserve
      (OriginSnapshot f.cf_fn f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) inst'
        (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))])` >>
  `joint_transition C8
      (JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h)
      (SOME (OriginResume fuel fn rinst s ret s_end s')) dst` by
    (simp[Abbr `dst`] >> irule joint_transition_ret >> simp[]) >>
  drule_all dft_packet_return_frame >> strip_tac >>
  fs[CONS_11] >>
  qpat_x_assum `dst = JointConfig _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qhdtm_x_assum `joint_transition` kall_tac >>
  drule_all dft_packet_return_cursor >> strip_tac >>
  PairCases_on `packet` >>
  rename1 `dft_focus_packet_rel _ _ _ _ _ _ (j,obs) _ _ _ _ _ _ _ _ _ _ _ _ _` >>
  drule_all dft_packet_current_body_cursor >> strip_tac >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  rename1 `FLOOKUP blocks ((e,cid)::a,d) =
    SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE)` >>
  rename1 `FLOOKUP acts ((e,cid)::a) = SOME (csf,fn,cinc,ent,cord,NONE,NONE)` >>
  `TAKE cn cxs = FRONT cxs /\ TAKE cn cys = FRONT cys` by
    (`cn = PRE (LENGTH cys)` by decide_tac >> metis_tac[TAKE_PRE_LENGTH]) >>
  `is_terminator rinst.inst_opcode /\ rinst.inst_opcode <> GAS /\
   rinst.inst_opcode <> INVOKE` by
    (qpat_assum `MEM rinst.inst_opcode [RET;RETFMP;DRET]` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[] >> strip_tac >> simp[venomInstTheory.is_terminator_def]) >>
  `step_inst (N-d) C8 rinst s = IntRet ret s_end` by
    fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `chbe < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by decide_tac >>
  `?after. trace_blocks [] 0 N C8 root_tf root_entry =
    TAKE chbe (trace_blocks [] 0 N C8 root_tf root_entry) ++
    trace_block ((e,cid)::a) d (N-d) C8 fn cbt cbe ++ after` by
    (qpat_assum `chbe < LENGTH _` mp_tac >>
     qpat_assum `EL chbe _ = _` mp_tac >>
     qpat_assum `lookup_block cbe.vs_current_bb fn.fn_blocks = SOME cbt` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all native_trace_blocks_continuation >> strip_tac >> gvs[] >>
     metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
  qabbrev_tac `R = trace_blocks [] 0 N C8 root_tf root_entry` >>
  `cbe.vs_inst_idx + cn <= LENGTH cbt.bb_instructions` by simp[] >>
  `chbe <= LENGTH R` by decide_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE cn (DROP cbe.vs_inst_idx cbt.bb_instructions))` by simp[DROP_LENGTH_APPEND] >>
  `FOLDR (dft_exec_cons (N-d) C8) OK
    (TAKE cn (DROP cbe.vs_inst_idx cbt.bb_instructions)) cbe = OK s` by
    simp[DROP_LENGTH_APPEND, IgnAsm `TAKE cn cys = FRONT cys`] >>
  drule_all native_trace_embedded_prefix_cut >> strip_tac >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  `?cms ces cks. FLOOKUP ms_tab ((e,cid)::a,d) = SOME cms /\
    FLOOKUP es_tab ((e,cid)::a,d) = SOME ces /\
    FLOOKUP ks_tab ((e,cid)::a,d) = SOME cks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
        `FDOM blocks = FDOM ks_tab`, `FLOOKUP blocks ((e,cid)::a,d) = SOME _`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qpat_assum `!a e bb bt ps xs ys sched ini h0 body count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (qspecl_then [`(e,cid)::a`,`d`] (drule_then strip_assume_tac)) >>
  qpat_x_assum `FLOOKUP acts ((e,cid)::a) = SOME (sf',fn,inc',entry',order'',NONE,NONE)`
    (fn th => qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (csf,fn,cinc,ent,cord,NONE,NONE)`
       (map_every SUBST_ALL_TAC o CONJUNCTS o SRULE [th])) >>
  qpat_x_assum `FLOOKUP blocks ((e,cid)::a,d) = SOME (bb',bt',ps',xs',ys',rho'',in_state',h0',body_entry,count'',OK s,F,NONE)`
    (fn th => qpat_assum `FLOOKUP blocks ((e,cid)::a,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE)`
       (map_every SUBST_ALL_TAC o CONJUNCTS o SRULE [th])) >>
  qpat_x_assum `FLOOKUP acts ((e,cid)::a) = SOME (sf'',tf',inc'',entry'',_,res,nrest)`
    (fn th => qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (csf,fn,cinc,ent,cord,NONE,NONE)`
       (map_every SUBST_ALL_TAC o CONJUNCTS o SRULE [th])) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (qspecl_then [`(e,cid)::a`,`csf`,`fn`,`cinc`,`ent`,`cord`,`NONE`,`NONE`]
      (drule_then strip_assume_tac)) >>
  qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe n front closed brest ms ess ks.
    _ ==> LENGTH ms = LENGTH xs /\ _`
    (qspecl_then [`(e,cid)::a`,`d`,`cbb`,`cbt`,`cps`,`cxs`,`cys`,`crho`,
       `cin`,`ch0`,`cbe`,`chbe`,`cn`,`OK s`,`F`,`NONE`,`cms`,`ces`,`cks`]
      (drule_all_then strip_assume_tac)) >>
  qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts ((e,cid)::a) = _ ==> _`
    (qspecl_then [`csf`,`fn`,`cinc`,`ent`,`cord`,`NONE`,`NONE`]
      (drule_then assume_tac)) >>
  `MEM fn C8.ctx_functions /\ MEM root_tf C8.ctx_functions` by
    (`MAP dft_fn C7.ctx_functions = C8.ctx_functions` by
       (qpat_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        qspecl_then [`dft_fn`,`I`,`C7.ctx_functions`,`C8.ctx_functions`] mp_tac MAP_EQ_EVERY2 >>
        simp[MAP_ID, EQ_SYM_EQ] >> metis_tac[LIST_REL_LENGTH]) >>
     pop_assum (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> conj_tac >- (qexists `csf` >> simp[]) >>
     qexists `root_sf` >> simp[]) >>
  `wf_function fn` by
    (drule dftContractGasTheory.o1_ctx_shape_wf_functions >> simp[EVERY_MEM]) >>
  `PERM (MAP THE (FILTER IS_SOME (FLAT cms)) ++ s.vs_gas_readings) cbe.vs_gas_readings` by
    (irule (Q.INST_TYPE [`:'a` |-> `:num`, `:'b` |-> `:num list`,
       `:'c` |-> `:ir_function`, `:'d` |-> `:num list`]
        dftPacketPreterminalReadingsTheory.dft_packet_preterminal_readings) >>
     qpat_assum `FLOOKUP blocks ((e,cid)::a,d) = SOME _` (irule_at Any) >>
     qexistsl [`fn`,`root_tf`,`root_entry`,`obs`,`j`,`rinst`,`calls`,`acts`,`R`,`N`,`C8`,`AM`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a sf tf inc entry order r8 u0.
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _`
          (drule_then strip_assume_tac) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (qx_gen_tac `v` >> disch_tac >>
           qpat_assum `!w. _ ==> _ /\ u0 = w.vs_gas_readings`
             (qspec_then `v` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
        (simp[])) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> disch_then (fn call =>
          qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
            FLOOKUP calls (a,e,cid) = _ ==> _` (fn info => mp_then Any mp_tac info call)) >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> strip_tac >>
        simp[]) >>
     conj_tac >- simp[] >>
     conj_tac >-
       (qpat_assum `!q. _ ==> MEM q (TAKE cn crho) /\ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     conj_tac >-
       (qpat_assum `(!q. q < LENGTH cxs ==> _) /\ (!ff k kgss tail. _)`
          (mp_tac o CONJUNCT1) >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     conj_tac >-
       (qpat_assum `(!q. q < LENGTH cxs ==> _) /\ (!ff k kgss tail. _)`
          (mp_tac o CONJUNCT1) >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[] >>
        Cases_on `FLOOKUP calls ((e,cid)::a,d,(EL q cxs).inst_id)` >> simp[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- simp[Abbr `R`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `TAKE cn cys = FRONT cys` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `case SOME (cbe,chbe) of NONE => _ | SOME x => _`
    (strip_assume_tac o SRULE []) >>
  qspecl_then [`acts`,`blocks`,`calls`,`N`,`C7`,`C8`,`root_tf`,`root_entry`,`j`,
    `chbe`,`(e,cid)::a`,`d`,`csf`,`fn`,`cbb`,`cbt`,`cps`,`cxs`,`cys`,`crho`,
    `cn`,`rinst`,`cbe`,`s`,`cms`,`ces`,`cks`,`obs`,`AM`,`AK`,`ms_tab`,`es_tab`,`ks_tab`]
    mp_tac dftPacketPreterminalNativeAgreementTheory.dft_packet_preterminal_native_agreement >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`lookup_block cbb.bb_label csf.fn_blocks = SOME cbb`,
           `MEM csf C7.ctx_functions`, `o1_ctx_shape C7`] >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[dftContractGasTheory.o1_ctx_shape_wf_functions, EVERY_MEM,
          venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def,
          venomWfTheory.wf_function_def]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
          (drule_then strip_assume_tac) >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> disch_then (fn row =>
          qpat_assum `!a e bb bt ps xs ys rho ini h0 body count front closed brest.
            FLOOKUP blocks (a,e) = _ ==> _` (fn info => mp_then Any mp_tac info row)) >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
        Cases_on `body_entry` >> gvs[]) >>
     conj_tac >-
       (map_every qx_gen_tac [`ap`,`ep`] >> rpt gen_tac >> strip_tac >>
        qpat_assum `!x v bb bt ps xs ys rho ini h0 be hbe n front closed brest ms ess ks.
          _ ==> LENGTH ms = LENGTH xs /\ _`
          (qspecl_then [`ap`,`ep`] (drule_all_then strip_assume_tac)) >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        `?sf tf inc entry order res nrest. FLOOKUP acts ap =
          SOME (sf,tf,inc,entry,order,res,nrest)` by
          (qpat_assum `!a e bb bt ps xs ys rho ini h0 body count front closed brest.
             FLOOKUP blocks (a,e) = _ ==> _`
             (qspecl_then [`ap`,`ep`] (drule_then strip_assume_tac)) >>
           goal_assum (drule_at Any)) >>
        qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts ap = _ ==> _`
          (drule_then (mp_tac o CONJUNCT1)) >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >> rpt gen_tac >> strip_tac >>
        first_x_assum drule >> simp[] >> rpt strip_tac >>
        rename1 `FLOOKUP calls key` >> Cases_on `FLOOKUP calls key` >> gvs[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> disch_then (fn call =>
          qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
            FLOOKUP calls (a,e,cid) = _ ==> _` (fn info => mp_then Any mp_tac info call)) >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
        goal_assum (drule_at Any) >> Cases_on `ret'` >> gvs[] >>
        PairCases_on `x` >> gvs[]) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a sf tf inc entry order r8 u0.
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _`
          (drule_then strip_assume_tac) >>
        qx_gen_tac `v` >> disch_tac >>
        qpat_assum `!w. _ ==> EVERY IS_SOME _ /\ _`
          (qspec_then `v` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (goal_assum (drule_at Any)) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (map_every qx_gen_tac [`ff`,`k`,`kgss`,`tail`,`u`] >> strip_tac >>
        qpat_assum `(!q. q < LENGTH cxs ==> _) /\ (!ff k kgss tail. _)`
          (qspecl_then [`ff`,`k`,`kgss`,`tail`] (drule_all_then strip_assume_tac) o CONJUNCT2) >>
        qpat_assum `!t. (?extra. FLAT (TAKE k ces) = _) /\ _`
          (qspec_then `tail` (qspec_then `u` (drule_then (ACCEPT_TAC o CONJUNCT1)) o CONJUNCT2))) >>
     rpt gen_tac >> strip_tac >>
     MATCH_MP_TAC dft_packet_call_supplier >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (csf,fn,cinc,ent,cord,NONE,NONE)` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks ((e,cid)::a,d) = SOME (cbb,cbt,cps,cxs,cys,crho,cin,ch0,SOME (cbe,chbe),cn,OK s,F,NONE)` (irule_at Any) >>
     qpat_assum `FLOOKUP ms_tab ((e,cid)::a,d) = SOME cms` (irule_at Any) >>
     qpat_assum `FLOOKUP ks_tab ((e,cid)::a,d) = SOME cks` (irule_at Any) >>
     qpat_assum `FOLDR (dft_exec_cons _ C7) OK (TAKE _ cxs) _ = OK _` (irule_at Any) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[])) >>
  strip_tac >>
  `EL (LENGTH ordered) cms = [] /\ EL (LENGTH ordered) ces = [] /\
   EL (LENGTH ordered) cks = []` by
    (irule dftPacketPreterminalRowsTheory.dft_packet_preterminal_empty_terminal >>
     qexistsl [`rinst`,`cxs`] >>
     reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `(!q. q < LENGTH cxs ==> _) /\ (!ff k kgss tail. _)`
       (drule_then strip_assume_tac o CONJUNCT1) >>
     qpat_assum `(EL _ cxs).inst_opcode <> GAS /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `LENGTH cms = LENGTH ordered + 1 /\ LENGTH ces = LENGTH ordered + 1 /\
   LENGTH cks = LENGTH ordered + 1` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH cms = LENGTH cxs`, `LENGTH ces = LENGTH cms`,
        `LENGTH cks = LENGTH cms`, `cxs = ordered ++ [rinst]`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `FLAT (TAKE (LENGTH ordered) cms) = FLAT cms /\
   FLAT (TAKE (LENGTH ordered) ces) = FLAT ces /\
   FLAT (TAKE (LENGTH ordered) cks) = FLAT cks` by
    (rpt conj_tac >>
     qmatch_goalsub_rename_tac `FLAT (TAKE (LENGTH ordered) cells)` >>
     qpat_assum `LENGTH cells = LENGTH ordered + 1` mp_tac >>
     qpat_assum `EL (LENGTH ordered) cells = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> strip_tac >>
     `TAKE (LENGTH ordered + 1) cells = cells` by
       (qpat_assum `LENGTH cells = _` (fn th => rewrite_tac[GSYM th, TAKE_LENGTH_ID])) >>
     qspecl_then [`cells`,`LENGTH ordered`] mp_tac TAKE_EL_SNOC >>
     simp[SNOC_APPEND] >>
     disch_then (fn th => CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV th)))) >> simp[]) >>
  qspecl_then [`N`,`d`,`C7`,`C8`,`csf`,`cbb`,`cps`,`cxs`,`cys`,`ordered`,`executed`,
    `rinst`,`cbe`,`s`,`IntRet ret s_end`,`s_end`,`cms`,`ces`,`cks`,`(e,cid)::a`]
    mp_tac dftPacketSuccessfulTerminalRowTheory.dft_packet_successful_terminal_row >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `EVERY _ (FRONT cxs)` mp_tac >>
        qpat_assum `cxs = ordered ++ [rinst]` SUBST1_TAC >> simp[FRONT_APPEND]) >>
     conj_tac >-
       (qpat_assum `EVERY _ (FRONT cys)` mp_tac >>
        qpat_assum `cys = executed ++ [rinst]` SUBST1_TAC >> simp[FRONT_APPEND]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >-
       (qpat_assum `!ff. N <= ff ==> FOLDR _ OK (TAKE cn cys) cbe = OK s` mp_tac >>
        qpat_assum `cys = executed ++ [rinst]` SUBST1_TAC >>
        qpat_assum `cn = LENGTH executed` SUBST1_TAC >> simp[NoAsms, TAKE_APPEND]) >>
     conj_tac >-
       (qpat_assum `EVERY IS_SOME (FLAT (TAKE (LENGTH ordered) cms))` mp_tac >>
        qpat_assum `FLAT (TAKE (LENGTH ordered) cms) = _` (fn th => rewrite_tac[th]) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     map_every qx_gen_tac [`ff`,`gs`,`tail`] >> strip_tac >>
     `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
       (FLAT (TAKE (LENGTH ordered) cms)) gs` by
       (qpat_assum `FLAT (TAKE (LENGTH ordered) cms) = _` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     drule dftPacketFillingBoundaryTheory.dft_packet_flat_filling_split >>
     disch_then (qx_choose_then `kgss` strip_assume_tac) >>
     qpat_assum `!ff kgss tail. N <= ff /\ LIST_REL _ (TAKE (LENGTH ordered) cms) kgss ==> _`
       (qspecl_then [`ff`,`kgss`,`tail`] (drule_all_then mp_tac)) >>
     qpat_assum `gs = FLAT kgss` SUBST1_TAC >>
     map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
       [`FLAT (TAKE (LENGTH ordered) ces) = _`, `FLAT (TAKE (LENGTH ordered) cks) = _`] >> simp[])) >>
  strip_tac >>
  `FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,TAKE count' rho',ent,NONE)` by
    (qpat_assum `!v id parent. (e,cid)::a = (v,id)::parent ==> _`
       (qspecl_then [`e`,`cid`,`a`] mp_tac) >>
     qpat_assum `FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,TAKE count' rho',child_entry,NONE)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `cinc = e` by
    (qpat_assum `cinc = case _ of _ => _ | _ => _` mp_tac >> simp[NoAsms]) >>
  pop_assum SUBST_ALL_TAC >>
  mp_tac
    (dftPacketReturnEdgeAssemblyTheory.dft_packet_return_edge_clauses_readings
     |> Q.INST [`readings_of` |-> `(gas_readings : 'a -> bytes32 list)`]
     |> Q.SPECL [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`j`,`obs`,
          `acts`,`blocks`,`calls`,`ms_tab`,`es_tab`,`ks_tab`]
     |> Q.INST [`b` |-> `(e,cid)::a`, `stk` |-> `f'::rest`, `f` |-> `f'`,
          `c` |-> `EL q xs`, `ir` |-> `ret`, `out` |-> `s_end`,
          `post` |-> `s'`, `next` |-> `inst''`, `r` |-> `rinst`, `ctf` |-> `fn`,
          `pbb` |-> `bb`, `pbt` |-> `bt`, `pps` |-> `ps`, `pxs` |-> `xs`,
          `pys` |-> `ys`, `prho` |-> `rho'`, `pin` |-> `in_state`, `ph0` |-> `h0`,
          `pbe` |-> `be`, `phbe` |-> `hbe`, `pn` |-> `count'`,
          `done` |-> `TAKE count' rho'`]) >>
  (impl_tac >-
    (rpt (conj_tac >- FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
     conj_tac >- goal_assum (drule_at Any) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a e bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
           _ ==> LENGTH ms = LENGTH xs /\ _` (drule_all_then strip_assume_tac) >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        rpt gen_tac >> strip_tac >>
        qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts _ = _ ==> _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `EVERY IS_SOME (FLAT (TAKE (LENGTH ordered) cms))` mp_tac >>
        qpat_assum `FLAT (TAKE (LENGTH ordered) cms) = _` (fn th => rewrite_tac[th]) >> simp[]) >>
     conj_tac >-
       qpat_assum `!F. N <= F ==> FOLDR _ OK cys cbe = IntRet ret s_end /\ _`
         (ACCEPT_TAC o SRULE []) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a e bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
           _ ==> LENGTH ms = LENGTH xs /\ _` (drule_all_then strip_assume_tac) >>
        qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts _ = _ ==> _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >>
        disch_then (fn hyps => first_assum (fn th => ACCEPT_TAC (MATCH_MP th hyps)))) >>
     rpt gen_tac >> strip_tac >>
     `FDOM ms_tab = FDOM ms_tab` by REFL_TAC >>
     `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP ms_tab key = SOME new ==>
        LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new` by
       (POP_ASSUM_LIST (K all_tac) >> rw[] >> gvs[] >>
        irule EVERY2_refl >> simp[EVERY2_refl]) >>
     drule_all_then strip_assume_tac
       (dft_packet_cut_row_alignment |> SPEC_ALL |> Q.INST [`W` |-> `ms_tab`]) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qexistsl [`N`,`obs`,`acts'`,`blocks'`,`calls'`,`ms_tab'`,`es_tab'`,`ks_tab'`,
            `a`,`e`,`raw_slots'`,`sites'`,`unused'`] >>
  conj_tac >- simp[] >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      map_every qx_gen_tac [`path0`,`depth0`,`id0`,`ix0`,`at0`,`b0'`,`done0`,`ent0`,`ret0`] >>
      strip_tac >>
      Cases_on `(path0,depth0,id0) = (a,e,cid)`
      >- (qexists_tac `SOME (ret,s_end,s')` >>
          map_every (fn pat => qpat_assum pat mp_tac)
            [`FLOOKUP calls (path0,depth0,id0) = _`, `(path0,depth0,id0) = (a,e,cid)`,
             `FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,TAKE count' rho',ent,NONE)`,
             `calls' = _`] >>
          POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[FLOOKUP_UPDATE]) >>
      qexists_tac `ret0` >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP calls (path0,depth0,id0) = _`, `(path0,depth0,id0) <> (a,e,cid)`,
         `calls' = _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> simp[FLOOKUP_UPDATE]) >>
  pure_rewrite_tac [pairTheory.FST] >>
  rewrite_tac[dft_focus_packet_rel_def] >>
  qexistsl [`SUC j`,`obs`,`AM`,`AE`,`AK`,`row_eval`,`plan_eval`,`call_setup`,
            `plan_ok`,`levels_ok`,`rest`,`f'.cf_params`,
            `DRESTRICT f'.cf_prov (COMPL (set (EL q xs).inst_outputs))`,
            `tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set (EL q xs).inst_outputs))`,
            `tf`,`inst''`,`s' with vs_inst_idx := SUC b0.vs_inst_idx`,`oms'`,
            `DRESTRICT caller_om' (COMPL (set (EL q xs).inst_outputs))`,`hs'`,
            `caller_h' ++ [OriginResume fuel fn rinst s ret s_end s';
               OriginObserve (OriginSnapshot tf f'.cf_params
                 (DRESTRICT f'.cf_prov (COMPL (set (EL q xs).inst_outputs)))
                 (DRESTRICT caller_om' (COMPL (set (EL q xs).inst_outputs))) inst''
                 (s' with vs_inst_idx := SUC b0.vs_inst_idx))]`] >>
  conj_tac >- REFL_TAC >>
  conj_tac >- (qpat_assum `b0.vs_inst_idx = _` (fn th => rewrite_tac[th])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl [`nm`,`lbl`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `trace_gas (TAKE (SUC j) _) = obs` (ACCEPT_TAC o SYM)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 3 (conj_tac >- (once_rewrite_tac[FUN_EQ_THM] >> BETA_TAC >> first_assum ACCEPT_TAC)) >>
  conj_tac >-
    (qpat_assum `unused' = _` (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- goal_assum (drule_at Any) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >>
     rename1 `FLOOKUP blocks' (_,_) = SOME (_,_,_,_,_,_,_,_,row_body,_,_,_,_)` >>
     namedCases_on `row_body` ["", "bhp"] >-
       (qpat_assum `!x v b t ps xs ys rho ini h0 body count front closed brest.
          FLOOKUP blocks' _ = _ ==> _` drule >> simp[NoAsms]) >>
     PairCases_on `bhp` >>
     qpat_assum `!x v b t ps xs ys rho ini h0 body count front closed brest.
          FLOOKUP blocks' _ = _ ==> _` drule >> simp[NoAsms]) >>
  conj_tac >-
    (qexistsl [`sf`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho'`,`in_state`,
              `h0`,`SOME (be,hbe)`,`SUC count'`] >> simp[NoAsms] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (map_every (fn q => qpat_assum q (fn th => rewrite_tac[th]))
       [`ms_tab' = ms_tab`,`es_tab' = es_tab`,`ks_tab' = ks_tab`] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!x f bb bt ps xs ys rho ini h0 be hbe count front closed brest ms ess ks.
        _ ==> LENGTH ms = LENGTH xs /\ _` (drule_all_then strip_assume_tac) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >> conj_tac >- (first_x_assum drule >> simp[]) >>
     qpat_assum `!x f bb bt ps xs ys rho ini h0 be hbe count front closed brest
        ms ess ks sf tf inc entry order res nrest.
        FLOOKUP blocks' (x,f) = _ /\ FLOOKUP ms_tab (x,f) = _ /\
        FLOOKUP es_tab (x,f) = _ /\ FLOOKUP ks_tab (x,f) = _ /\
        FLOOKUP acts' x = _ ==> !F k kgss tail. _` mp_tac >>
     qmatch_asmsub_rename_tac `FLOOKUP blocks' (ra,re) = SOME (_,_,_,_,_,_,_,_,_,_,_,_,_)` >>
     qpat_assum `FLOOKUP blocks' (ra,re) = SOME _` mp_tac >>
     qpat_assum `FLOOKUP ms_tab (ra,re) = SOME _` mp_tac >>
     qpat_assum `FLOOKUP es_tab (ra,re) = SOME _` mp_tac >>
     qpat_assum `FLOOKUP ks_tab (ra,re) = SOME _` mp_tac >>
     qpat_assum `FLOOKUP acts' ra = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 5 disch_tac >>
     disch_then drule >> ASM_SIMP_TAC bool_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
     disch_tac >> map_every qx_gen_tac [`F0`,`k0`,`gss0`,`tail0`] >> disch_tac >>
     qpat_assum `!F k kgss tail. _ ==> (?extra. _) /\ _`
       (qspecl_then [`F0`,`k0`,`gss0`,`tail0`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (map_every (fn q => qpat_assum q (fn th => rewrite_tac[th]))
       [`ms_tab' = ms_tab`,`es_tab' = es_tab`,`ks_tab' = ks_tab`] >>
     first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest.
        FLOOKUP blocks' _ = _ ==> _` mp_tac >>
     qpat_assum `!x sf tf inc entry order res nrest.
        FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts' a = _`,`FLOOKUP blocks' (a,e) = _`,
        `SUC count' < LENGTH ys`,`inst'' = EL (SUC count') ys`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     qpat_x_assum `!x v bb bt ps xs ys rho ini h0 body count front closed brest. _`
       (drule_then strip_assume_tac) >>
     gvs[optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
     qpat_x_assum `!x sf tf inc entry order res nrest.
        FLOOKUP acts' x = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
       (drule_then (assume_tac o cj 3)) >>
     strip_tac >>
     `from_block [EL (EL (SUC count') rho') xs] (EL (SUC count') ys)` by
       (qpat_assum `LIST_REL _ rho' ys` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        qpat_assum `!n. n < LENGTH rho' ==> _` (qspec_then `SUC count'` mp_tac) >>
        (impl_tac >- asm_rewrite_tac[]) >>
        disch_then (ACCEPT_TAC o cj 3 o BETA_RULE)) >>
     `EL (EL (SUC count') rho') xs = EL (SUC count') ys` by
       metis_tac[dft_packet_guard_from_block, MEM] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule dft_packet_memory_schedule_predecessors >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  rpt gen_tac >>
  rename1 `_ /\ FLOOKUP blocks' (cut_a,cut_e) =
    SOME (_,_,_,_,_,_,_,_,row_body,_,_,_,_) /\ _ ==> _` >>
  namedCases_on `row_body` ["", "bhp"] >-
    (rewrite_tac[optionTheory.IS_SOME_DEF] >> strip_tac >>
     qpat_x_assum `cut_a = a` SUBST_ALL_TAC >>
     qpat_x_assum `cut_e = e` SUBST_ALL_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks' (a,e) = SOME (_,_,_,_,_,_,_,_,NONE,_,_,_,_)`,
        `FLOOKUP blocks' (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
  PairCases_on `bhp` >>
  rewrite_tac[optionTheory.IS_SOME_DEF,optionTheory.NOT_SOME_NONE] >> strip_tac >>
  qpat_assum `!x f sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count front closed brest q z.
    FLOOKUP acts' x = _ /\ FLOOKUP blocks' (x,f) = _ /\ _ ==> ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (drule_all_then mp_tac) >>
  map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [GSYM (SPEC_ALL th)]))
    [`!x. AM x = _`,`!x. AE x = _`,`!x. AK x = _`] >>
  disch_then ACCEPT_TAC
QED

Theorem dft_focus_packet_step_retained:
  !(N:num) (C7:venom_context) C8 (root_sf:ir_function) (root_tf:ir_function)
    (root_entry:venom_state) packet
    (acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab : (((num # num) list # num), bytes32 option list list) fmap)
    (es_tab : (((num # num) list # num), (string # num) list list) fmap)
    (ks_tab : (((num # num) list # num), gas_event list list) fmap)
    rooted_eval p d cpl es0 raw_slots sites unused
    stk PG G tn fn inst s oms om hs h ev q8'.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    (inst.inst_opcode = GAS ==> s.vs_gas_readings <> []) /\
    joint_transition C8 (JointConfig stk PG G tn fn inst s oms om hs h) ev q8' ==>
    (?N' obs' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d'
      raw_slots' sites' unused'.
      N <= N' /\
      dft_focus_packet_rel N' C7 C8 root_sf root_tf root_entry
        (SUC (FST packet),obs') acts' blocks' calls' ms_tab' es_tab' ks_tab'
        rooted_eval p' d' q8' raw_slots' sites' unused' /\
      LENGTH raw_slots' = LENGTH sites' /\
      PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0) /\
      (!a e cid ix h b0 done_at_call child_entry ret.
        FLOOKUP calls (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret) ==>
        ?ret'. FLOOKUP calls' (a,e,cid) =
          SOME (ix,h,b0,done_at_call,child_entry,ret') /\
          (IS_SOME ret ==> ret' = ret))) /\
    ( (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
       inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s ==>
      ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z
        cuts levels Mcut Ecut.
        FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
        LAST order = d /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE) /\
        q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
          MEM r (TAKE count rho)) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid call_h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        LENGTH Mcut = LENGTH Ecut /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            C7 (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom C7 sf inst u /\
          ~in_revert_forward sf u /\
          (inv_memory_observation inst.inst_opcode ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
            u.vs_initial_fmp = s.vs_initial_fmp)))
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (mp_tac dft_packet_source_projection >>
      (impl_tac >-
        (conj_tac
         >- (rpt gen_tac >> MATCH_ACCEPT_TAC dft_packet_guarded_cursor)
         >> MATCH_ACCEPT_TAC dft_packet_trace_raw_reachable)) >>
      disch_then (drule_then MATCH_ACCEPT_TAC)) >>
  PairCases_on `packet` >> rename1 `dft_focus_packet_rel _ _ _ _ _ _ (j,obs) _ _ _ _ _ _ _ _ _ _ _ _ _` >>
  pure_rewrite_tac [pairTheory.FST] >>
  qhdtm_x_assum `joint_transition`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once joint_transition_cases])
  >- (`?sf inc entry order bb bt ps xs ys rho in_state h0 body_entry count.
          FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
          LAST order = d /\
          FLOOKUP blocks (p,d) =
            SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,OK s,F,NONE) /\
          lookup_block s.vs_current_bb fn.fn_blocks = SOME bt /\
          get_instruction bt s.vs_inst_idx = SOME inst /\
          (case body_entry of
            NONE => phi_prefix_length bt.bb_instructions <= s.vs_inst_idx /\
              s.vs_inst_idx < LENGTH ps /\ count = 0 /\
              FOLDR (dft_exec_cons (N-d) C8) OK
                (DROP (phi_prefix_length bt.bb_instructions) (TAKE s.vs_inst_idx ps))
                ((case eval_phis in_state bt.bb_instructions of
                  OK sp => sp | other => in_state)
                  with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s
          | SOME (be,hbe) => s.vs_inst_idx = LENGTH ps + count /\
              count < LENGTH ys /\ inst = EL count ys)` by
        (qhdtm_assum `dft_focus_packet_rel`
           (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS) o
             REWRITE_RULE [dft_focus_packet_rel_def]) >>
         qpat_x_assum `?sf inc entry order bb bt ps xs ys rho in_state h0 body_entry count.
           FLOOKUP acts p = SOME (sf,_,inc,entry,order,NONE,NONE) /\ _` mp_tac >>
         qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
      Cases_on `body_entry`
      >- suspend "pseudo" >>
      PairCases_on `x` >> suspend "next")
  >- suspend "block"
  >- suspend "call"
  >> suspend "return"
QED

Resume dft_focus_packet_step_retained[next]:
  rename1 `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),n,OK s,F,NONE)` >>
  qpat_x_assum `case SOME (be,hbe) of NONE => _ | SOME v => _`
    (strip_assume_tac o SRULE []) >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
  `wf_function fn` by
    (qhdtm_assum `dft_focus_packet_rel`
       (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS) o
         REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` drule >>
     strip_tac >>
     `MEM fn C8.ctx_functions` by
       (qpat_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
        qpat_assum `MEM sf C7.ctx_functions` mp_tac >>
        qpat_assum `fn = dft_fn sf` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_all LIST_REL_MEM_IMP >> simp[]) >>
     qpat_assum `MEM fn C8.ctx_functions` mp_tac >>
     qpat_assum `o1_ctx_shape C8` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM]) >>
  `get_instruction bt (SUC s.vs_inst_idx) = SOME inst''` by
    (`ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
     drule_all active_inst_lookup_distinct >> strip_tac >> gvs[]) >>
  `SUC n < LENGTH ys /\ inst'' = EL (SUC n) ys` by
    (`SUC s.vs_inst_idx = LENGTH ps + SUC n` by decide_tac >>
     qpat_assum `get_instruction bt (SUC s.vs_inst_idx) = _` mp_tac >>
     qpat_x_assum `SUC s.vs_inst_idx = _` SUBST1_TAC >>
     simp[venomInstTheory.get_instruction_def, EL_APPEND2]) >>
  `EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),fn,inst,s)` by
    (drule_all dft_packet_current_body_cursor >> simp[]) >>
  `SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
   EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
     ((p,d,inst''.inst_id),fn,inst'',s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule_all native_trace_blocks_continuation >> strip_tac >>
     `bt' = bt` by
       (qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bt` mp_tac >>
        qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bt'` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[optionTheory.SOME_11]) >>
     qpat_x_assum `bt' = bt` SUBST_ALL_TAC >>
     qpat_x_assum `DROP j _ = _` mp_tac >>
     drule_all dft_ordinary_trace_cons >> strip_tac >> simp[] >>
     simp[Once (cj 2 trace_defs)] >>
     qmatch_goalsub_abbrev_tac `DROP j tr = _` >>
     strip_tac >>
     `EL 1 (DROP j tr) = ((p,d,inst''.inst_id),fn,inst'',s' with vs_inst_idx := SUC s.vs_inst_idx)` by gvs[] >>
     `1 < LENGTH (DROP j tr)` by
       (qpat_assum `DROP j tr = _` SUBST1_TAC >> gvs[]) >>
     fs[LENGTH_DROP, EL_DROP, arithmeticTheory.ADD1, arithmeticTheory.ADD_COMM]) >>
  `TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) =
   TAKE j (trace_blocks [] 0 N C8 root_tf root_entry) ++ [((p,d,inst.inst_id),fn,inst,s)]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  irule dft_packet_body_next_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `FLOOKUP blocks (p,d) = SOME _`)) >>
  goal_assum (drule_at (Pat `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  simp[] >>
  reverse conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS) o
      REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _`
    drule >> strip_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` drule >> strip_tac >>
  qpat_x_assum `option_CASE (SOME (be,hbe)) _ _`
    (strip_assume_tac o SRULE [optionTheory.option_case_def, pairTheory.pair_case_thm]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
     `FLOOKUP acts p = SOME (_,_,_,_,_,_,_)`,
     `LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions`, `dft_fn_rel sf' tf`,
     `lookup_block bb.bb_label sf'.fn_blocks = SOME bb`,
     `lookup_block bb.bb_label tf.fn_blocks = SOME bt`,
     `bb.bb_instructions = ps ++ xs`, `bt.bb_instructions = ps ++ ys`,
     `EVERY (\i. is_pseudo i.inst_opcode) ps`,
     `EVERY (\i. ~is_pseudo i.inst_opcode) xs`, `EVERY inst_shape_ok _`,
     `bb_well_formed bt`, `dft_remaining_inv _ bb xs be`, `be.vs_inst_idx = LENGTH ps`,
     `q < LENGTH xs`, `SUC n < LENGTH ys`, `xs❲q❳ = ys❲SUC n❳`,
     `inv_memory_observation _`, `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs)`,
     `FOLDR _ _ _ _ = OK u`, `FOLDR _ _ (TAKE (SUC n) ys) be = OK _`,
     `trace_agrees _ (trace_block _ _ _ C7 _ _ _)`,
     `trace_agrees _ (trace_block _ _ _ C8 _ _ _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  `(∀op. MEM op (EL (SUC n) ys).inst_operands ==>
      eval_operand op u = eval_operand op (s' with vs_inst_idx := SUC (n + LENGTH ps))) /\
    u.vs_initial_fmp = (s' with vs_inst_idx := SUC (n + LENGTH ps)).vs_initial_fmp`
    suffices_by simp[] >>
  ho_match_mp_tac dft_packet_successor_observation_agreement >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK u`)) >>
  qexistsl_tac [`C8`, `sf`, `fn`, `bb`, `bt`, `bb.bb_label`, `ps`, `ys`,
    `p`, `d`, `N-d`, `orc`, `SUC n`] >>
  simp[arithmeticTheory.ADD_COMM] >>
  metis_tac[venomExecPropsTheory.FIND_MEM, venomInstTheory.lookup_block_def]
QED
Resume dft_focus_packet_step_retained[pseudo]:
  qpat_x_assum `case NONE of NONE => _ | SOME v => _`
    (strip_assume_tac o SRULE []) >>
  qpat_x_assum `_ = 0` SUBST_ALL_TAC >>
  qhdtm_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS) o
      REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  `wf_function fn` by
    (qpat_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` drule >>
     strip_tac >>
     `MEM fn C8.ctx_functions` by
       (qpat_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
        qpat_assum `MEM sf C7.ctx_functions` mp_tac >>
        qpat_assum `fn = dft_fn sf` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_all LIST_REL_MEM_IMP >> simp[]) >>
     qpat_assum `MEM fn C8.ctx_functions` mp_tac >>
     qpat_assum `o1_ctx_shape C8` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM]) >>
  qabbrev_tac `s1 = s' with vs_inst_idx := SUC s.vs_inst_idx` >>
  `get_instruction bt s1.vs_inst_idx = SOME inst''` by
    (`ALL_DISTINCT (fn_labels fn)` by
       (qpat_assum `wf_function fn` (mp_tac o REWRITE_RULE [venomWfTheory.wf_function_def]) >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     drule_all (Q.SPECL [`fn`,`inst''`,`s1`] active_inst_lookup_distinct) >>
     disch_then (qx_choose_then `bt_next` strip_assume_tac) >>
     `s1.vs_current_bb = s.vs_current_bb` by
       (drule_all venomInstPropsTheory.step_preserves_control_flow >> simp[Abbr `s1`]) >>
     `bt_next = bt` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`lookup_block s1.vs_current_bb fn.fn_blocks = SOME bt_next`,
           `lookup_block s.vs_current_bb fn.fn_blocks = SOME bt`,
           `s1.vs_current_bb = s.vs_current_bb`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qpat_x_assum `bt_next = bt` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  `is_pseudo inst.inst_opcode` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _`
       drule >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`get_instruction bt s.vs_inst_idx = SOME inst`,
        `EVERY (\i. is_pseudo i.inst_opcode) ps`,
        `s.vs_inst_idx < LENGTH ps`, `bt.bb_instructions = ps ++ ys`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[venomInstTheory.get_instruction_def, EL_APPEND1, EVERY_EL]) >>
  qspecl_then [`N`, `C7`, `C8`, `root_sf`, `root_tf`, `root_entry`,
    `acts`, `blocks`, `calls`, `ms_tab`, `es_tab`, `ks_tab`,
    `j`, `obs`, `AM`, `AE`, `AK`, `row_eval`, `plan_eval`, `call_setup`,
    `rooted_eval`, `plan_ok`, `levels_ok`, `p`, `d`, `fn`, `inst`, `s`,
    `sf`, `inc`, `entry`, `order`, `bb`, `bt`, `ps`, `xs`, `ys`, `rho'`,
    `in_state`, `h0`, `s.vs_inst_idx`, `phi_prefix_length ps`, `fuel`, `s'`,
    `s1`, `inst''`] mp_tac dftPacketPseudoNextClausesTheory.dft_packet_pseudo_next_clauses >>
  `s1 = s' with vs_inst_idx := SUC s.vs_inst_idx` by simp[Abbr `s1`] >>
  impl_tac >-
    (pure_rewrite_tac [EXISTS_SIMP] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  disch_then (qx_choose_then `blocks1` (qx_choose_then `ms_out`
    (qx_choose_then `es_out` (qx_choose_then `ks_out` (qx_choose_then `AM1`
      (qx_choose_then `AE1` (qx_choose_then `AK1`
        (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS))))))))) >>
  qexistsl_tac [`N`, `obs`, `acts`, `blocks1`, `calls`,
    `ms_out`, `es_out`, `ks_out`, `p`, `d`, `AM1 []`, `AE1 []`, `s1.vs_gas_readings`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (pure_rewrite_tac [dft_focus_packet_rel_def] >>
      qexistsl_tac [`SUC j`, `obs`, `AM1`, `AE1`, `AK1`, `row_eval`,
        `plan_eval`, `call_setup`, `plan_ok`, `levels_ok`, `stk`, `PG`,
        `step_prov PG G inst s'`, `step_taint inst s s' tn`, `fn`, `inst''`, `s1`,
        `oms`, `origin_step PG om inst s'`, `hs`,
        `h ++ [OriginOrdinary fuel s'; OriginObserve
          (OriginSnapshot fn PG (step_prov PG G inst s') (origin_step PG om inst s') inst'' s1)]`] >>
      qpat_assum `FDOM blocks1 = FDOM blocks` (fn dom =>
        qpat_assum `!a sf tf inc entry order res nrest.
          FLOOKUP acts a = _ ==> MEM sf _ /\ _`
          (assume_tac o PURE_REWRITE_RULE [GSYM dom])) >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, REFL_TAC, first_assum (ACCEPT_TAC o SYM),
        (qexistsl_tac [`sf`, `inc`, `entry`, `order`, `bb`, `bt`, `ps`, `xs`, `ys`,
           `rho'`, `in_state`, `h0`,
           `if SUC s.vs_inst_idx < LENGTH ps then NONE else SOME (s1,SUC j)`, `0`] >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- (qpat_assum `blocks1 = _` SUBST1_TAC >> simp[FLOOKUP_UPDATE, NoAsms])) >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `(if SUC s.vs_inst_idx < LENGTH ps then _ else _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `SUC s.vs_inst_idx < LENGTH ps` >> simp[])]) >>
  once_rewrite_tac [CONJ_ASSOC] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `ret` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!g0. PERM (MAP THE (FILTER IS_SOME (AM [])) ++ s.vs_gas_readings) g0 ==> _` irule >>
  qpat_assum `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) _` mp_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`raw_slots = AM []`, `unused = s.vs_gas_readings`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED
(* Select only the old packet clauses needed by each block-edge premise. *)
val activation = `!a sf tf inc entry order res nrest.
  FLOOKUP acts a = _ ==> MEM sf C7.ctx_functions /\ _`;
val visit = `!a e bb bt ps xs ys rho hin h0 body count front closed brest.
  FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`;
val call = `!a e cid q h b0 done child ret.
  FLOOKUP calls (a,e,cid) = _ ==> ?sf tf inc entry order res nrest. _`;
val row = `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
  FLOOKUP blocks (a,e) = _ /\ _ ==> LENGTH ms = LENGTH xs /\ _`;
val row_owner = `!sf tf inc entry order res nrest.
  FLOOKUP acts _ = _ ==> (!q. q < LENGTH _ ==> _) /\ _`;
val project = fn pat => qpat_assum pat (drule_then strip_assume_tac);
val project_row = qpat_assum row (drule_all_then strip_assume_tac);
val invoke_cell =
  qpat_assum `!q. q < LENGTH _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `(EL q xs).inst_opcode = INVOKE ==> _` mp_tac >>
  qpat_assum `(EL q xs).inst_opcode = INVOKE` mp_tac >>
  qmatch_goalsub_rename_tac `FLOOKUP calls (a,e,(EL q xs).inst_id)` >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `FLOOKUP calls (a,e,(EL q xs).inst_id)` >> simp[];
val call_visit =
  map_every qx_gen_tac [`pathv`,`ed`,`idv`,`col`,`atj`,`pre`,`donev`,`entc`,`rval`] >>
  disch_tac >>
  qpat_assum call
    (qspecl_then [`pathv`,`ed`,`idv`,`col`,`atj`,`pre`,`donev`,`entc`,`rval`] mp_tac) >>
  qpat_assum `FLOOKUP calls (pathv,ed,idv) = SOME _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> disch_then (fn th => rewrite_tac[th]) >>
  strip_tac >>
  qpat_assum `FLOOKUP blocks (pathv,ed) = SOME _` (irule_at Any) >>
  rpt conj_tac >> FIRST
    [first_assum ACCEPT_TAC,
     (qpat_assum `_ = EL col _` SUBST_ALL_TAC >> first_assum ACCEPT_TAC),
     (qpat_assum `case rval of NONE => _ | SOME (_,_,_) => _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      namedCases_on `rval` ["","triple"] >> simp[] >>
      PairCases_on `triple` >> simp[])];
Resume dft_focus_packet_step_retained[block]:
  `~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >>
     gvs[venomInstTheory.is_pseudo_def, venomInstTheory.is_terminator_def]) >>
  drule_all dft_packet_return_data >> strip_tac >>
  rename1 `ct < LENGTH ys` >>
  `is_terminator (EL ct ys).inst_opcode /\ (EL ct ys).inst_opcode <> INVOKE` by
    metis_tac[] >>
  drule_all dft_packet_return_geometry >> strip_tac >>
  `!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
     MEM q (TAKE ct rho')` by
    metis_tac[dft_packet_return_schedule] >>
  drule_all dft_packet_current_body_cursor >> strip_tac >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  `?ms ess ks. FLOOKUP ms_tab (p,d) = SOME ms /\
     FLOOKUP es_tab (p,d) = SOME ess /\ FLOOKUP ks_tab (p,d) = SOME ks` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
        `FDOM blocks = FDOM ks_tab`, `FLOOKUP blocks (p,d) = _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  drule_all dft_packet_selected_body >> strip_tac >>
  `!F q kgss tail u.
     N <= F /\ q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
     MEM q (TAKE ct rho') /\
     EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
     (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE ct rho')) /\
     LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms kgss /\
     FOLDR (dft_exec_cons (F-d) C7) OK (TAKE q xs)
       (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
     (?extra. EL q ks = MAP FST (trace_gas
       (trace_step p d (F-d) C7 sf (EL q xs) u)) ++ extra) /\
     (!v. step_inst (F-d) C7 (EL q xs) u = OK v ==>
       EL q ks = MAP FST (trace_gas (trace_step p d (F-d) C7 sf (EL q xs) u)))` by
    (rpt gen_tac >> strip_tac >> drule_all dft_packet_call_supplier >> simp[]) >>
  `?ordered executed.
     xs = ordered ++ [inst] /\ ys = executed ++ [inst] /\
     ct = LENGTH executed /\ LENGTH ordered = LENGTH executed /\
     EVERY IS_SOME (FLAT (TAKE (LENGTH ordered) ms)) /\
     (!F kgss tail.
       N <= F /\ LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
         (TAKE (LENGTH ordered) ms) kgss ==>
       FOLDR (dft_exec_cons (F-d) C7) OK ordered
         (be with vs_gas_readings := FLAT kgss ++ tail) = OK (s with vs_gas_readings := tail) /\
       gas_events_block (F-d) C7 sf.fn_name
         <|bb_label := be.vs_current_bb; bb_instructions :=
           REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ ordered|>
         (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE (LENGTH ordered) ess) /\
       trace_gas (trace_block p d (F-d) C7 sf
         (bb with bb_instructions := TAKE (LENGTH ps + LENGTH ordered) bb.bb_instructions)
         (be with vs_gas_readings := FLAT kgss ++ tail)) =
         ZIP (FLAT (TAKE (LENGTH ordered) ks),FLAT kgss))` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     map_every (fn pat => qpat_x_assum pat
       (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o SIMP_RULE (srw_ss()) []))
       [`(j,obs) = _`, `JointConfig stk PG G tn fn inst s oms om hs h = _`] >>
     irule dftPacketPreterminalNativeAgreementTheory.dft_packet_preterminal_native_agreement >>
     `bb_well_formed bb` by
       (qpat_assum `dft_fn_rel sf fn` mp_tac >>
        qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[dft_fn_rel_def, venomWfTheory.wf_function_def,
                  simplifyCfgDefsTheory.lookup_block_member_label]) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (qexistsl [`AK`, `AM`, `C8`, `acts`, `blocks`, `bt`, `calls`, `es_tab`,
           `hbe`, `j`, `ks_tab`, `ms_tab`, `obs`, `root_entry`, `root_tf`, `rho'`, `fn`] >>
         rpt conj_tac
         >- (qpat_assum `!a sf tf inc entry order r8 u0.
               FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> metis_tac[])
         >- (qpat_assum activation mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> metis_tac[])
         >- (qpat_assum visit mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             strip_tac >> rpt gen_tac >> disch_tac >>
             first_x_assum (drule_then strip_assume_tac) >>
             conj_tac >- metis_tac[] >> strip_tac >> gvs[])
         >- (rpt gen_tac >> strip_tac >> project visit >> project_row >> project row_owner >>
             ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
             qx_gen_tac `i` >> disch_tac >>
             first_x_assum (drule_then strip_assume_tac) >>
             rename1 `i < LENGTH rowxs` >>
             map_every (fn pat => qpat_assum pat mp_tac)
               [`(EL i rowxs).inst_opcode = GAS ==> _`,
                `(EL i rowxs).inst_opcode <> GAS /\ _ ==> _`,
                `(EL i rowxs).inst_opcode = INVOKE ==> _`] >>
             POP_ASSUM_LIST (K all_tac) >>
             Cases_on `FLOOKUP calls (a,e,(EL i rowxs).inst_id)` >> simp[SF CONJ_ss])
         >- first_assum ACCEPT_TAC
         >- (qpat_assum call mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> strip_tac >> rpt gen_tac >> disch_tac >>
             first_x_assum (drule_then strip_assume_tac) >>
             conj_tac >- metis_tac[] >>
             rename1 `FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest)` >>
             qexistsl [`csf`, `ctf`, `child_order`, `child_res`, `child_rest`] >>
             simp[] >> rpt strip_tac >> gvs[])
         >- first_assum ACCEPT_TAC
         >- (project_row >>
             qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts p = _ ==> _`
               (fn th => qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`
                 (mp_then Any strip_assume_tac th)) >>
             rpt gen_tac >> strip_tac >>
             qpat_assum `!F k kgss tail. _ ==> (?extra. _) /\ !u. _`
               (drule_all_then (qspec_then `tail` strip_assume_tac)) >>
             qpat_assum `!u. FOLDR _ _ _ _ = OK u ==> _`
               (drule_then strip_assume_tac) >>
             first_assum ACCEPT_TAC) >>
         FIRST [first_assum ACCEPT_TAC,
           (qexistsl [`in_state`, `h0`] >> first_assum ACCEPT_TAC),
           (qpat_assum `lookup_function _ C8.ctx_functions = SOME root_tf`
              (mp_tac o MATCH_MP venomInstTheory.lookup_function_MEM) >> simp[])])]) >>
  `inst.inst_opcode <> GAS` by
    (strip_tac >> fs[venomInstTheory.is_terminator_def]) >>
  `LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
   EL (LENGTH ordered) ms = [] /\ EL (LENGTH ordered) ess = [] /\
   EL (LENGTH ordered) ks = []` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
       FLOOKUP blocks (a,e) = _ /\ _ ==> _` (drule_all_then strip_assume_tac) >>
     qpat_x_assum `!sf tf inc entry order res nrest. FLOOKUP acts p = _ ==> _`
       (fn th => qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`
         (mp_then Any strip_assume_tac th)) >>
     qpat_assum `xs = ordered ++ [inst]` (fn th =>
       `LENGTH ordered < LENGTH xs` by simp[NoAsms, th]) >>
     qpat_x_assum `!q. q < LENGTH xs ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `(EL (LENGTH ordered) xs).inst_opcode <> GAS /\ _ ==> _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ms = LENGTH xs`, `LENGTH ess = LENGTH ms`, `LENGTH ks = LENGTH ms`,
        `xs = ordered ++ [inst]`, `inst.inst_opcode <> GAS`, `inst.inst_opcode <> INVOKE`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[EL_LENGTH_APPEND_0]) >>
  `FLAT (TAKE (LENGTH ordered) ms) = FLAT ms /\
   FLAT (TAKE (LENGTH ordered) ess) = FLAT ess /\
   FLAT (TAKE (LENGTH ordered) ks) = FLAT ks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ms = LENGTH xs`, `LENGTH ess = LENGTH ms`, `LENGTH ks = LENGTH ms`,
        `xs = ordered ++ [inst]`, `EL (LENGTH ordered) ms = []`,
        `EL (LENGTH ordered) ess = []`, `EL (LENGTH ordered) ks = []`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> rpt conj_tac >>
     qmatch_goalsub_rename_tac `FLAT (TAKE (LENGTH ordered) row)` >>
     `TAKE (LENGTH ordered) row ++ [EL (LENGTH ordered) row] = row` by
       (irule vyperMiscTheory.TAKE_SNOC_EL >> simp[]) >>
     `FLAT (TAKE (LENGTH ordered) row ++ [EL (LENGTH ordered) row]) = FLAT row` by
       (AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
     pop_assum mp_tac >> simp[FLAT_APPEND]) >>
  `step_inst (N-d) C8 inst s = OK s'` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `EVERY IS_SOME (FLAT ms)` by
    (qpat_assum `FLAT (TAKE (LENGTH ordered) ms) = FLAT ms` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK executed be = OK s` by
    (qpat_assum `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK (TAKE ct ys) be = OK s` mp_tac >>
     qpat_assum `ct = LENGTH executed` (fn th => rewrite_tac[th]) >>
     qpat_assum `ys = executed ++ [inst]` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, TAKE_LENGTH_APPEND]) >>
  `!F gs tail. N <= F /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
       FOLDR (dft_exec_cons (F-d) C7) OK ordered
         (be with vs_gas_readings := gs ++ tail) = OK (s with vs_gas_readings := tail) /\
       gas_events_block (F-d) C7 sf.fn_name
         <|bb_label := be.vs_current_bb;
           bb_instructions := REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ ordered|>
         (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
       trace_gas (trace_block p d (F-d) C7 sf
         (bb with bb_instructions := TAKE (LENGTH ps + LENGTH ordered) bb.bb_instructions)
         (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)` by
    (rpt gen_tac >> strip_tac >>
     `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE (LENGTH ordered) ms)) gs` by
       (qpat_assum `FLAT (TAKE (LENGTH ordered) ms) = _` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     dxrule dftPacketFillingBoundaryTheory.dft_packet_flat_filling_split >> strip_tac >>
     qpat_assum `!F kgss tail. N <= F /\ _ ==> _` (drule_all_then (qspec_then `tail` mp_tac)) >>
     map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
       [`gs = FLAT _`, `FLAT (TAKE (LENGTH ordered) ess) = _`,
        `FLAT (TAKE (LENGTH ordered) ks) = _`] >>
     simp[NoAsms]) >>
  qabbrev_tac `R = trace_blocks [] 0 N C8 root_tf root_entry` >>
  qabbrev_tac `prefix_bt = bt with bb_instructions := TAKE (be.vs_inst_idx + ct) bt.bb_instructions` >>
  `hbe < LENGTH R /\ hbe <= LENGTH R` by decide_tac >>
  `TAKE j R = TAKE hbe R ++ trace_block p d (N-d) C8 fn prefix_bt be` by
    (`?rest. R = TAKE hbe R ++ trace_block p d (N-d) C8 fn bt be ++ rest` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`EL hbe R = _`, `lookup_block be.vs_current_bb fn.fn_blocks = SOME bt`,
           `hbe < LENGTH R`, `Abbrev (R = _)`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >> rpt strip_tac >> gvs[] >>
        drule_all dftPacketNativeContinuationTheory.native_trace_blocks_continuation >>
        strip_tac >> gvs[] >> metis_tac[TAKE_DROP, APPEND_ASSOC]) >>
     qpat_assum `Abbrev (prefix_bt = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     irule dftPacketNativeSliceTheory.native_trace_embedded_prefix_cut >>
     `TAKE ct (DROP be.vs_inst_idx bt.bb_instructions) = TAKE ct ys` by
       (map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
          [`be.vs_inst_idx = _`, `bt.bb_instructions = _`] >>
        rewrite_tac[DROP_LENGTH_APPEND]) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`be.vs_inst_idx = _`, `ct < LENGTH ys`, `bt.bb_instructions = _`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[])
     >- (qexists `rest` >> first_assum ACCEPT_TAC)
     >- (qexistsl [`inst`,`s`] >>
         qpat_assum `TAKE ct (DROP _ _) = _` (fn th => rewrite_tac[th]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`TAKE ct (DROP _ _) = _`, `EVERY _ (FRONT ys)`,
        `ct = LENGTH executed`, `ys = executed ++ [inst]`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[TAKE_LENGTH_APPEND, FRONT_APPEND]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ordered /\
   EVERY (\i. ~is_terminator i.inst_opcode) executed` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY _ (FRONT xs)`, `EVERY _ (FRONT ys)`,
        `xs = ordered ++ [inst]`, `ys = executed ++ [inst]`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[FRONT_APPEND]) >>
  `PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ s.vs_gas_readings)
     be.vs_gas_readings` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_x_assum `(j,obs) = _`
       (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
       FLOOKUP blocks (a,e) = _ /\ _ ==> LENGTH ms = LENGTH xs /\ _`
       (drule_all_then strip_assume_tac) >>
     `MEM sf C7.ctx_functions /\ fn = dft_fn sf` by
       (qpat_assum `!a sf tf inc entry order res nrest.
           FLOOKUP acts a = _ ==> MEM sf C7.ctx_functions /\ _`
          mp_tac >>
        qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     `wf_function fn` by
       (`MEM fn C8.ctx_functions` by
          (qpat_assum `LIST_REL (\f g. g = dft_fn f) _ _` mp_tac >>
           qpat_assum `MEM sf C7.ctx_functions` mp_tac >>
           qpat_assum `fn = dft_fn sf` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
           drule_all LIST_REL_MEM_IMP >> simp[]) >>
        qpat_assum `MEM fn C8.ctx_functions` mp_tac >>
        qpat_assum `o1_ctx_shape C8` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[o1_ctx_shape_wf_functions, EVERY_MEM]) >>
     `LENGTH ys = SUC ct` by decide_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE ct ys)` by
       (map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
          [`ct = LENGTH executed`,`ys = executed ++ [inst]`] >>
        simp[NoAsms,TAKE_LENGTH_APPEND] >> first_assum ACCEPT_TAC) >>
     irule (Q.INST_TYPE [`:'a` |-> `:num`, `:'b` |-> `:num list`,
                         `:'c` |-> `:ir_function`, `:'d` |-> `:num list`]
       dftPacketPreterminalReadingsTheory.dft_packet_preterminal_readings) >>
     qexistsl [`AM`,`C8`,`N`,`R`,`p`,`acts`,`bb`,`blocks`,`bt`,`calls`,`ct`,`d`,
       `h0`,`hbe`,`in_state`,`inst`,`j`,`obs`,`ps`,`root_entry`,`root_tf`,`rho'`,`fn`,`xs`,`ys`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `!a sf tf inc entry order r8 u0. FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     conj_tac >-
       (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
          FLOOKUP calls (a,e,cid) = _ ==> ?sf tf. _` mp_tac >>
        qpat_assum `FLOOKUP calls (p,d,cid) = SOME (_,_,_,_,_,SOME _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        disch_then (fn th => disch_then (mp_tac o SRULE [] o (C MATCH_MP) th)) >>
        strip_tac >> rpt (goal_assum $ drule_at Any) >> simp[]) >>
     `!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==>
          EL q ms = [ALOOKUP obs (p,d,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q ms = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          case FLOOKUP calls (p,d,(EL q xs).inst_id) of
            NONE => EL q ms = []
          | SOME call => EL q ms = AM ((d,(EL q xs).inst_id)::p))` by
       (qpat_assum `!sf tf inc entry order res nrest.
           FLOOKUP acts p = _ ==> (!q. q < LENGTH xs ==> _) /\ _`
          (drule_then (mp_tac o CONJUNCT1)) >>
        POP_ASSUM_LIST (K all_tac) >> disch_tac >> gen_tac >>
        first_x_assum (qspec_then `q` mp_tac) >>
        Cases_on `FLOOKUP calls (p,d,(EL q xs).inst_id)` >> simp[] >> metis_tac[]) >>
     pop_assum (mk_asm "cells") >>
     conj_tac >- (asm "cells" mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     conj_tac >-
       (qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
           FLOOKUP blocks (a,e) = _ ==> !q. _` drule >> simp[]) >>
     conj_tac >- (asm "cells" mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     conj_tac >- (asm "cells" mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     `TAKE j R = TAKE hbe R ++ trace_block p d (N-d) C8 fn
        (bt with bb_instructions := TAKE (ct + be.vs_inst_idx) bt.bb_instructions) be` by
       (qpat_assum `TAKE j R = TAKE hbe R ++ _` mp_tac >>
        qpat_assum `Abbrev (prefix_bt = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        rewrite_tac[markerTheory.Abbrev_def] >> strip_tac >> gvs[arithmeticTheory.ADD_COMM]) >>
     `R = trace_blocks [] 0 N C8 root_tf root_entry` by simp[Abbr `R`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (rename1 `TAKE j R = TAKE hbe R ++ _` >>
        qpat_assum `TAKE j R = TAKE hbe R ++ trace_block _ _ _ _ _ (bt with bb_instructions := _) _`
          mp_tac >>
        qpat_assum `R = trace_blocks [] 0 N C8 root_tf root_entry` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[])]) >>
  qspecl_then [`N`,`d`,`C7`,`C8`,`sf`,`bb`,`ps`,`xs`,`ys`,`ordered`,`executed`,
    `inst`,`be`,`s`,`OK s'`,`s'`,`ms`,`ess`,`ks`,`p`] mp_tac
    dftPacketSuccessfulTerminalRowTheory.dft_packet_successful_terminal_row >>
  impl_tac >-
    (rpt conj_tac >> rpt (first_assum ACCEPT_TAC) >> simp[NoAsms] >>
     first_assum ACCEPT_TAC) >>
  disch_then (fn th => assume_tac th >> map_every assume_tac (CONJUNCTS th)) >>
  suspend "block_edge_assembly"
QED
Resume dft_focus_packet_step_retained[block_edge_assembly]:
  qhdtm_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS) o
      REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  qpat_x_assum `JointConfig stk PG G tn fn inst s oms om hs h = _`
    (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o PURE_REWRITE_RULE [joint_config_11]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> MEM sf _ /\ _`
    (drule_then strip_assume_tac) >>
  `lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb /\
   strict_dom_vars_defined sf in_state /\ fn_reachable sf in_state.vs_current_bb /\
   ctx_labels_bound C7 in_state.vs_labels /\ ctx_labels_bound C8 in_state.vs_labels` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
      FLOOKUP blocks (a,e) = _ ==> _` (drule_then mp_tac) >>
     qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss] >> metis_tac[]) >>
  `eval_phis in_state bt.bb_instructions = OK sp /\
   FOLDR (dft_exec_cons (N-d) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
     (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be` by
    (qpat_assum `bt.bb_instructions = ps ++ ys` (fn th => rewrite_tac[th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!F. FOLDR (dft_exec_cons (F-d) C8) OK _ _ = OK be`
       (qspec_then `N` ACCEPT_TAC)) >>
  `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK s'` by
    (qpat_assum `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK s' /\ _`
       (mp_tac o cj 1) >> simp[NoAsms]) >>
  mp_tac (dftPacketBlockEdgeClausesTheory.dft_packet_block_edge_clauses
    |> Q.INST [`ks` |-> `ks_tab`]
    |> Q.INST [`rsf` |-> `root_sf`, `tf` |-> `fn`, `m` |-> `ms_tab`,
       `es` |-> `es_tab`, `keys` |-> `ks`, `hin` |-> `in_state`,
       `rho0` |-> `rho'`, `cnt0` |-> `ct`, `pre` |-> `ordered`,
       `post` |-> `s'`, `next` |-> `inst''`]) >>
  impl_tac >> rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
       >- (qpat_assum `?seq. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,seq,NONE,NONE)`
             (qx_choose_then `root_order` assume_tac) >>
           qexistsl [`root_sf`,`root_tf`,`0`,`root_entry`,`root_order`,`NONE`,`NONE`] >>
           first_assum ACCEPT_TAC)
       >- (rpt gen_tac >> strip_tac >> project activation >>
           rpt conj_tac >> first_assum ACCEPT_TAC)
       >- (qx_gen_tac `i` >> strip_tac >>
           qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys sched
             hin h0 be hbe count. _` (qspec_then `i` mp_tac) >>
           qpat_assum `i < LENGTH p` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])
       >- (rpt gen_tac >> strip_tac >>
           qpat_assum call (drule_then mp_tac) >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[])
       >- (rpt gen_tac >> strip_tac >> strip_tac >>
           qpat_assum visit (drule_then mp_tac) >>
           qpat_assum `_ = (NONE : (venom_state # num) option)` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])
       >- (rpt gen_tac >> strip_tac >> project_row >> project visit >> project row_owner >>
           rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
           qx_gen_tac `ix` >> strip_tac >>
           qpat_assum `!q. q < LENGTH _ ==> _ /\ _ /\ _`
             (qspec_then `ix` mp_tac) >>
           qpat_assum `ix < LENGTH _` mp_tac >>
           qmatch_goalsub_rename_tac `FLOOKUP calls (a,e,(EL ix xrow).inst_id)` >>
           POP_ASSUM_LIST (K all_tac) >>
           Cases_on `FLOOKUP calls (a,e,(EL ix xrow).inst_id)` >> simp[SF CONJ_ss])
       >- (rpt gen_tac >> strip_tac >> project_row >>
           (conj_tac >- first_assum ACCEPT_TAC) >>
           rpt gen_tac >> strip_tac >> project row_owner >>
           qx_gen_tac `ix` >> strip_tac >>
           qpat_assum `!q. q < LENGTH _ ==> _ /\ _ /\ _`
             (qspec_then `ix` mp_tac) >>
           qpat_assum `ix < LENGTH _` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss])
       >- (qpat_assum `LENGTH (AM []) = LENGTH (AK [])` (ACCEPT_TAC o SYM))
       >- (map_every qx_gen_tac [`fuel'`,`filling`,`suffix`] >> strip_tac >>
           qpat_assum `!F kgss tail. N <= F /\ LIST_REL _ (TAKE (LENGTH ordered) ms) kgss ==> _`
             (qspecl_then [`fuel'`,`filling`,`suffix`] mp_tac o cj 1) >>
           qpat_assum `LIST_REL _ (TAKE (LENGTH ordered) ms) filling` mp_tac >>
           qpat_assum `N <= fuel'` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> simp[])
       >- (rpt gen_tac >> strip_tac >>
           qpat_assum `!a sf tf inc entry order r8 u0. FLOOKUP acts a = _ ==> terminates r8 /\ _`
             (drule_then strip_assume_tac) >>
           qpat_assum `!F. N <= F ==> run_blocks _ _ _ _ = _ /\ _`
             (qspec_then `N` mp_tac) >> POP_ASSUM_LIST (K all_tac) >> simp[])
       >- call_visit
       >- (map_every qx_gen_tac [`a`,`e`,`brow`,`trow`,`prow`,`xrow`] >>
           rpt gen_tac >> disch_tac >> conj_tac
           >- (project visit >> project activation >>
               qmatch_asmsub_rename_tac `lookup_block brow.bb_label owner.fn_blocks = SOME brow` >>
               `MEM brow owner.fn_blocks /\ wf_function owner` by
                 (qpat_assum `dft_fn_rel owner _` mp_tac >>
                  qpat_assum `lookup_block brow.bb_label owner.fn_blocks = SOME brow` mp_tac >>
                  POP_ASSUM_LIST (K all_tac) >>
                  metis_tac[dft_fn_rel_def, venomExecPropsTheory.FIND_MEM,
                            venomInstTheory.lookup_block_def]) >>
               drule_all dftWfTheory.wf_fn_block_inst_ids_distinct >>
               qpat_assum `brow.bb_instructions = prow ++ xrow` SUBST1_TAC >>
               POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT_APPEND]) >>
           `?mrow erow krow. FLOOKUP ms_tab (a,e) = SOME mrow /\
             FLOOKUP es_tab (a,e) = SOME erow /\ FLOOKUP ks_tab (a,e) = SOME krow` by
             (map_every (fn pat => qpat_assum pat mp_tac)
               [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
                `FDOM blocks = FDOM ks_tab`,`FLOOKUP blocks (a,e) = SOME _`] >>
              POP_ASSUM_LIST (K all_tac) >>
              metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
           project_row >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`FLOOKUP ms_tab (a,e) = SOME mrow`,`FLOOKUP es_tab (a,e) = SOME erow`,
              `FLOOKUP ks_tab (a,e) = SOME krow`,`LENGTH mrow = LENGTH xrow`,
              `LENGTH erow = LENGTH mrow`,`LENGTH krow = LENGTH mrow`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss])
       >- (rpt gen_tac >> strip_tac >> project activation >> first_assum ACCEPT_TAC)
       >- (map_every qx_gen_tac [`a`,`e`,`cid`,`idx`,`visit_h`,`caller`,`done`,`child`,
                                  `ret_ir`,`ret_out`,`ret_post`] >> strip_tac >> project call >>
           qpat_x_assum `case SOME (ret_ir,ret_out,ret_post) of NONE => _ | SOME _ => _`
             (strip_assume_tac o SRULE []) >>
           qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (_,_,e,child,_,_,_)` mp_tac >>
           qpat_assum `_ = SOME (IntRet ret_ir ret_out)` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[])
       >- (rpt gen_tac >> strip_tac >> project_row >> project row_owner >> first_assum ACCEPT_TAC)
       >- (rpt gen_tac >> strip_tac >> project_row >> project visit >> project row_owner >> simp[])
       >- (rpt gen_tac >> strip_tac >> project activation >>
           rpt conj_tac >> first_assum ACCEPT_TAC)
       >- (rpt gen_tac >> strip_tac >> project visit >>
           conj_tac >- (rpt (goal_assum $ drule_at Any) >> simp[]) >>
           rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
             (strip_tac >>
              qpat_assum `case body_entry of NONE => _ | SOME _ => _` mp_tac >>
              qpat_assum `body_entry = NONE` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss])])
       >- (rpt gen_tac >> strip_tac >> project_row >> project visit >> project row_owner >>
           rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])
       >- call_visit
  >> disch_then (List.foldr (fn (q,k) => qx_choose_then q k)
    (map_every assume_tac o CONJUNCTS)
    [`N1`,`bb1`,`bt1`,`sp1`,`ps1`,`xs1`,`ys1`,`sched1`,`body1`,`cm`,`ce`,`ck`,
     `acts1`,`blocks1`,`calls1`,`inds`,`ms1`,`es1`,`ks1`,`AM1`,`AE1`,`AK1`]) >>
  qpat_x_assum `calls1 = calls` SUBST_ALL_TAC >>
  qexistsl_tac [`N1`, `obs`, `acts1`, `blocks1`, `calls`,
    `ms1`, `es1`, `ks1`, `p`, `SUC d`, `AM1 []`, `AE1 []`, `s1.vs_gas_readings`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (pure_rewrite_tac [dft_focus_packet_rel_def] >>
      qexistsl_tac [`SUC j`, `obs`, `AM1`, `AE1`, `AK1`, `row_eval`,
        `plan_eval`, `call_setup`, `plan_ok`, `levels_ok`, `stk`, `PG`,
        `entry_prov fn s' G`, `entry_taint_vars fn s' tn`, `fn`, `inst''`, `s1`,
        `oms`, `origin_entry fn s' om`, `hs`,
        `h ++ [OriginBlock fuel s'; OriginObserve
          (OriginSnapshot fn PG (entry_prov fn s' G) (origin_entry fn s' om) inst'' s1)]`] >>
      rpt (FIRST [first_assum ACCEPT_TAC, REFL_TAC, conj_tac])
      >- (map_every (fn pat => qpat_assum pat mp_tac)
            [`obs = trace_gas (TAKE j R)`, `Abbrev (R = _)`,
             `trace_gas (TAKE (SUC j) (trace_blocks [] 0 N1 C8 root_tf root_entry)) = _`] >>
          POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def])
      >- (qpat_assum `s1.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- (qpat_assum `MAP _ (FILTER _ (ZIP (AK1 [],AM1 []))) = _` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- (pure_rewrite_tac [EXISTS_SIMP] >> first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe cnt front closed brest mr er kr.
         FLOOKUP blocks1 (a,e) = _ /\ FLOOKUP ms1 (a,e) = SOME mr /\ _ ==> LENGTH mr = LENGTH xs /\ _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!key mr er kr. FLOOKUP ms1 key = SOME mr /\ FLOOKUP es1 key = SOME er /\
           FLOOKUP ks1 key = SOME kr ==> _` (drule_all_then strip_assume_tac) >>
      qpat_assum `!a e kr. FLOOKUP ks1 (a,e) = SOME kr ==> ALL_DISTINCT (FLAT kr)`
        (drule_all_then assume_tac) >>
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum (ACCEPT_TAC o SYM)
      >- first_assum (ACCEPT_TAC o SYM)
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      conj_tac
      >- (qx_gen_tac `ix` >> strip_tac >>
          qpat_assum `!f g ai ent ord r u. FLOOKUP acts1 _ = SOME _ ==> !q. _`
            (drule_then (qspec_then `ix` mp_tac)) >>
          qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
             FLOOKUP blocks1 (a,e) = _ /\ FLOOKUP ms1 (a,e) = SOME ms /\ _ ==>
             !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==> _`
            mp_tac >>
          map_every (fn pat => qpat_assum pat mp_tac)
            [`ix < LENGTH _`, `FLOOKUP blocks1 (a,e) = SOME _`,
             `FLOOKUP ms1 (a,e) = SOME _`, `FLOOKUP es1 (a,e) = SOME _`,
             `FLOOKUP ks1 (a,e) = SOME _`] >>
          POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
      qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed brest ms ess keys
                        sf tf inc entry order res nrest.
         FLOOKUP blocks1 (a,e) = _ /\ FLOOKUP ms1 (a,e) = SOME ms /\
         FLOOKUP es1 (a,e) = SOME ess /\ FLOOKUP ks1 (a,e) = SOME keys /\
         FLOOKUP acts1 a = SOME (sf,tf,inc,entry,order,res,nrest) ==> !F k kgss tail. _`
        (qspecl_then [`a`,`e`] mp_tac) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP blocks1 (a,e) = SOME _`, `FLOOKUP ms1 (a,e) = SOME _`,
         `FLOOKUP es1 (a,e) = SOME _`, `FLOOKUP ks1 (a,e) = SOME _`,
         `FLOOKUP acts1 a = SOME _`] >>
      POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss] >>
      ntac 6 disch_tac >> map_every qx_gen_tac [`FF`,`kk`,`gg`,`tt`] >> strip_tac >>
      qpat_x_assum `!F k kgss tail. _` (qspecl_then [`FF`,`kk`,`gg`,`tt`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (assume_tac o CONJUNCT2) >> rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  once_rewrite_tac [CONJ_ASSOC] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> qexists_tac `ret` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) _` mp_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`raw_slots = AM []`, `unused = s.vs_gas_readings`,
     `s1.vs_gas_readings = s.vs_gas_readings`,
     `MAP THE (FILTER IS_SOME (AM1 [])) = MAP THE (FILTER IS_SOME (AM []))`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED
Resume dft_focus_packet_step_retained[call]:
  `~is_pseudo inst.inst_opcode` by simp[venomInstTheory.is_pseudo_def] >>
  drule_all dft_packet_return_data >> strip_tac >>
  drule_all dft_packet_current_body_cursor >> strip_tac >>
  drule_all dft_packet_body_native_data >> strip_tac >>
  `?ms ess ks. FLOOKUP ms_tab (p,d) = SOME ms /\
     FLOOKUP es_tab (p,d) = SOME ess /\ FLOOKUP ks_tab (p,d) = SOME ks` by
    (qhdtm_assum `dft_focus_packet_rel` mp_tac >>
     rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
        `FDOM blocks = FDOM ks_tab`, `FLOOKUP blocks (p,d) = _`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  rename1 `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,OK s,F,NONE)` >>
  qabbrev_tac `q = EL cnt sched` >>
  `q = EL cnt sched` by simp[Abbr `q`] >>
  drule_all dft_packet_call_rooted_setup >> strip_tac >>
  `~MEM q (TAKE cnt sched)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`q = EL cnt sched`, `PERM sched (COUNT_LIST (LENGTH xs))`,
        `cnt < LENGTH ys`, `LENGTH xs = LENGTH ys`] >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     `LENGTH sched = LENGTH xs` by metis_tac[sortingTheory.PERM_LENGTH, LENGTH_COUNT_LIST] >>
     `ALL_DISTINCT sched` by metis_tac[sortingTheory.ALL_DISTINCT_PERM, all_distinct_count_list] >>
     qpat_x_assum `MEM _ (TAKE cnt sched)` mp_tac >>
     simp[MEM_EL] >> rpt strip_tac >>
     `n < LENGTH sched /\ cnt < LENGTH sched` by decide_tac >>
     `EL cnt sched = EL n sched` by fs[EL_TAKE] >>
     `n = cnt` by metis_tac[ALL_DISTINCT_EL_IMP] >> decide_tac) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_block bb.bb_label sf.fn_blocks = SOME bb`,
        `dft_fn_rel sf fn`, `bb.bb_instructions = ps ++ xs`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `wf_function sf /\ MEM bb sf.fn_blocks` by
       metis_tac[dft_fn_rel_def,venomExecProofsTheory.lookup_block_MEM] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
       (irule dftWfTheory.wf_fn_block_inst_ids_distinct >> qexists_tac `sf` >> simp[]) >>
     pop_assum mp_tac >> simp[ALL_DISTINCT_APPEND]) >>
  qhdtm_assum `dft_focus_packet_rel`
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS) o
      REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `(j,obs) = _`
    (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  qpat_x_assum `JointConfig stk PG G tn fn inst s oms om hs h = _`
    (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o PURE_REWRITE_RULE [joint_config_11]) >>
  `raw_reachable root_entry C8 fn inst s` by
    (qpat_assum `?nm lbl. C7.ctx_entry = SOME nm /\ _` strip_assume_tac >>
     `fn_entry_label root_tf = SOME lbl` by simp[dftCorrectnessFinalTheory.dft_fn_entry_label] >>
     `MEM ((p,d,inst.inst_id),fn,inst,s) (trace_blocks [] 0 N C8 root_tf root_entry)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`,
           `EL j (trace_blocks [] 0 N C8 root_tf root_entry) = _`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        simp[MEM_EL] >> qexists_tac `j` >> simp[]) >>
     drule_all_then ACCEPT_TAC dft_packet_trace_raw_reachable) >>
  drule_then assume_tac o1PassLiftTheory.raw_reachable_labels >>
  `ctx_labels_bound C7 s.vs_labels /\ ctx_labels_bound C8 s.vs_labels` by simp[] >>
  `!a e. (a,e) IN FDOM blocks ==> a IN FDOM acts` by
    (rpt strip_tac >>
     `?row. FLOOKUP blocks (a,e) = SOME row` by
       (qpat_assum `(a,e) IN FDOM blocks` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF]) >>
     PairCases_on `row` >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest. FLOOKUP blocks _ = _ ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP acts a = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> IF_CASES_TAC >> simp[]) >>
  qspecl_then
    [`acts`,`blocks`,`calls`,`N`,`C7`,`C8`,`root_tf`,`root_entry`,`j`,
     `p`,`d`,`inst`,`s`,`sf`,`fn`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,
     `ys`,`sched`,`hin`,`h0`,`be`,`hbe`,`cnt`,`q`,`nm`,`ops`,`callee`,`args`,
     `cs`,`s1`,`inst'`,`stk`,`PG`,`G`,`tn.t_var`] mp_tac
    dftPacketCallRecordJoinTheory.dft_packet_call_record_preservation >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
          (drule_then strip_assume_tac) >>
        rpt (goal_assum (drule_at Any)) >>
        qpat_x_assum `case ret of NONE => _ | SOME _ => _` mp_tac >>
        namedCases_on `ret` ["", "retv"] >- simp[] >>
        PairCases_on `retv` >> simp[] >> rpt strip_tac >> first_assum ACCEPT_TAC)) >>
     first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qabbrev_tac `bpath = (d,inst.inst_id)::p` >>
  qabbrev_tac `plen = LENGTH bpath` >>
  qabbrev_tac `inds = q::GENLIST (\i.
    FST (THE (FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p)` >>
  qabbrev_tac `ords = GENLIST (\i. if i = 0 then [SUC d] else
    FST (SND (SND (SND (SND (THE (FLOOKUP acts (DROP i bpath)))))))) (SUC plen)` >>
  `!i. 0 < i /\ i < plen ==>
     ?pre h b0 done child eb tb eps exs eys erho ein eh ebe ehbe ecnt.
       FLOOKUP calls (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath)) =
         SOME (pre,h,b0,done,child,NONE) /\
       FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) =
         SOME (eb,tb,eps,exs,eys,erho,ein,eh,SOME (ebe,ehbe),ecnt,OK b0,F,NONE) /\
       pre < LENGTH exs /\ EL i inds = pre` by
    ((unabbrev_all_tac >> Cases_on `i` >> simp[EL, EL_GENLIST] >> strip_tac >>
     qpat_assum `!k. k < LENGTH p ==>
       ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
        q h b0 done child cid e a. _` (qspec_then `n` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_x_assum `(e,cid) = EL n p` (assume_tac o SYM) >>
     qpat_x_assum `a = DROP (SUC n) p` SUBST_ALL_TAC >>
     simp[] >>
     rpt (goal_assum (drule_at Any)) >>
     qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
       (drule_then strip_assume_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks (DROP (SUC n) p,e) =
          SOME (_,_,_,xs',_,_,_,_,_,_,OK b0,F,NONE)`,
        `FLOOKUP blocks (DROP (SUC n) p,e) =
          SOME (_,_,_,xs'',_,_,_,_,_,_,front,closed,brest)`,
        `q < LENGTH xs''`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> (metis_tac[EL, EL_GENLIST]))) >>
  `!i. i < plen ==> ?eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0.
      FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) =
        SOME (eb,tb,eps,exs,eys,erho,ein,eh,SOME (ebe,ehbe),ecnt,OK eb0,F,NONE) /\
      EL i inds < LENGTH exs` by
    (rpt strip_tac >> Cases_on `i = 0`
     >- (qpat_x_assum `i = 0` SUBST_ALL_TAC >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP blocks (p,d) = SOME _`, `q < LENGTH xs`,
            `Abbrev (bpath = _)`, `Abbrev (inds = _)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >>
         rpt strip_tac >> gvs[EL] >> rpt (goal_assum (drule_at Any))) >>
     `0 < i` by (qpat_assum `i <> 0` mp_tac >> simp[arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
     qpat_assum `!i. 0 < i /\ i < plen ==> ?pre h b0 done child eb tb eps exs eys erho ein eh ebe ehbe ecnt. _`
       (drule_all_then strip_assume_tac) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!i. i < plen ==> ?m e k.
      FLOOKUP ms_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME m /\
      FLOOKUP es_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME e /\
      FLOOKUP ks_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME k /\
      EL i inds < LENGTH m /\ EL i inds < LENGTH e /\ EL i inds < LENGTH k` by
    (rpt strip_tac >>
     qpat_assum `!i. i < plen ==> ?eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _`
       (drule_then strip_assume_tac) >>
     `?m e k.
       FLOOKUP ms_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME m /\
       FLOOKUP es_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME e /\
       FLOOKUP ks_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME k` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`FDOM blocks = FDOM ms_tab`, `FDOM blocks = FDOM es_tab`,
          `FDOM blocks = FDOM ks_tab`,
          `FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) = SOME _`] >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        _ ==> LENGTH ms = LENGTH xs /\ _` (drule_all_then strip_assume_tac) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `bpath = (d,inst.inst_id)::p /\ plen = LENGTH bpath /\
   LENGTH inds = plen /\ HD inds = q /\ LENGTH ords = SUC plen /\ HD ords = [SUC d]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (bpath = _)`, `Abbrev (plen = _)`,
        `Abbrev (inds = _)`, `Abbrev (ords = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> rw[markerTheory.Abbrev_def, HD_GENLIST]) >>
  `!i. 0 < i /\ i <= plen ==> ?osf otf oi oen ores orest.
      FLOOKUP acts (DROP i bpath) = SOME (osf,otf,oi,oen,EL i ords,ores,orest)` by
    (rpt gen_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (ords = _)`, `bpath = (d,inst.inst_id)::p`, `plen = LENGTH bpath`,
        `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
        `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
          q h b0 done child cid e a. _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt (disch_then assume_tac) >>
     Cases_on `i` >- gvs[] >> gvs[markerTheory.Abbrev_def] >>
     Cases_on `n` >- (simp[EL_GENLIST] >> rpt (goal_assum (drule_at Any))) >>
     `n' < LENGTH p` by gvs[] >>
     first_x_assum (drule_then strip_assume_tac) >>
     simp[EL_GENLIST] >> rpt (goal_assum (drule_at Any))) >>
  `!i. 0 < i /\ i < plen ==> ?ch b0 done child.
      FLOOKUP calls (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath)) =
        SOME (EL i inds,ch,b0,done,child,NONE)` by
    (rpt strip_tac >>
     qpat_assum `!i. 0 < i /\ i < plen ==> ?pre h b0 done child eb tb eps exs eys erho ein eh ebe ehbe ecnt. _`
      (drule_all_then strip_assume_tac) >>
     qpat_x_assum `EL i inds = _` SUBST1_TAC >> rpt (goal_assum (drule_at Any))) >>
  qabbrev_tac `has_body = IS_SOME cbe` >>
  `(has_body ==> s1.vs_inst_idx = LENGTH cps) /\
   (~has_body ==> s1.vs_inst_idx < LENGTH cps) /\
   cbe = (if has_body then SOME (s1,SUC j) else NONE)` by
    (qpat_assum `case cbe of NONE => _ | SOME _ => _` mp_tac >>
     qpat_assum `Abbrev (has_body = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >>
     Cases_on `cbe` >- simp[] >> PairCases_on `x` >> simp[]) >>
  qabbrev_tac `cm = if has_body then GENLIST (\r.
    if (EL r cxs).inst_opcode = GAS then [NONE:bytes32 option] else []) (LENGTH cxs) else []` >>
  qabbrev_tac `ce = if has_body then GENLIST (\r.
    if (EL r cxs).inst_opcode = GAS then [(csf.fn_name,(EL r cxs).inst_id)] else []) (LENGTH cxs) else []` >>
  qabbrev_tac `ck = if has_body then GENLIST (\r.
    if (EL r cxs).inst_opcode = GAS then [(bpath,SUC d,(EL r cxs).inst_id)] else []) (LENGTH cxs) else []` >>
  qspecl_then
    [`acts`,`blocks`,`calls`,`ms_tab`,`es_tab`,`ks_tab`,`p`,`d`,`inst`,`j`,`s`,`cnt`,
     `sched`,`q`,`csf`,`callee`,`cs`,`s1`,`cbb`,`cbt`,`cps`,`cxs`,`cys`,`crho`,
     `has_body`,`bpath`,`plen`,`inds`,`ords`,`cm`,`ce`,`ck`,`cbe`] mp_tac
    dftPacketCallUpdateTheory.dft_packet_call_tables >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     map_every (fn pat => conj_tac >-
       qpat_assum pat (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (cm = _)`, `Abbrev (ce = _)`, `Abbrev (ck = _)`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`acts'' = _`, `blocks'' = _`, `calls'' = _`,
     `!a. a <> bpath ==> FLOOKUP acts'' a = _`,
     `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks'' (a,e) = _`,
     `!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls'' key = _`,
     `FLOOKUP blocks'' (p,d) = _`] >>
  `!a e. (a,e) <> (bpath,SUC d) /\
     (!r. r < plen ==> (a,e) <> (DROP (SUC r) bpath,FST (EL r bpath))) ==>
     FLOOKUP ms' (a,e) = FLOOKUP ms_tab (a,e) /\
     FLOOKUP es' (a,e) = FLOOKUP es_tab (a,e) /\
     FLOOKUP ks' (a,e) = FLOOKUP ks_tab (a,e)` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
     conj_tac
     >- (qpat_assum `ms' = _` SUBST1_TAC >> first_assum irule >>
         conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
     conj_tac
     >- (qpat_assum `es' = _` SUBST1_TAC >> first_assum irule >>
         conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
     qpat_assum `ks' = _` SUBST1_TAC >> first_assum irule >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
  `!i. i < plen ==> DROP i bpath = (FST (EL i bpath),SND (EL i bpath))::DROP (SUC i) bpath` by
    (qpat_assum `plen = _` SUBST1_TAC >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[rich_listTheory.DROP_CONS_EL,pairTheory.PAIR]) >>
  `!a e value. FLOOKUP blocks (a,e) = SOME value ==> (a,e) <> (bpath,SUC d)` by
    (rpt strip_tac >> qpat_assum `!a e. (a,e) IN FDOM blocks ==> _` mp_tac >>
     qpat_assum `FLOOKUP acts bpath = NONE` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME value` mp_tac >>
     qpat_assum `(a,e) = (bpath,SUC d)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF] >> metis_tac[]) >>
  `!a e value rm re rk.
     FLOOKUP blocks (a,e) = SOME value /\
     FLOOKUP ms_tab (a,e) = SOME rm /\ FLOOKUP es_tab (a,e) = SOME re /\
     FLOOKUP ks_tab (a,e) = SOME rk ==>
     ((FLOOKUP ms' (a,e) = SOME rm /\ FLOOKUP es' (a,e) = SOME re /\
       FLOOKUP ks' (a,e) = SOME rk) \/
      ?i. i < plen /\ (a,e) = (DROP (SUC i) bpath,FST (EL i bpath)) /\
       FLOOKUP ms' (a,e) = SOME (LUPDATE
         (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (DROP i bpath,f)))) (EL i ords))) (EL i inds) rm) /\
       FLOOKUP es' (a,e) = SOME (LUPDATE
         (FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i bpath,f)))) (EL i ords))) (EL i inds) re) /\
       FLOOKUP ks' (a,e) = SOME (LUPDATE
         (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i bpath,f)))) (EL i ords))) (EL i inds) rk))` by
    (rpt strip_tac >> Cases_on `?i. i < plen /\ (a,e) = (DROP (SUC i) bpath,FST (EL i bpath))`
     >- (qpat_x_assum `?i. i < plen /\ (a,e) = _` (qx_choose_then `i` strip_assume_tac) >>
         disj2_tac >> qexists_tac `i` >>
         conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
         qpat_x_assum `(a,e) = _` (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS o SRULE []) >>
         map_every (fn pat => qpat_assum pat (qspec_then `i` (drule_all_then strip_assume_tac)))
           [`!i rows. i < plen /\ FLOOKUP ms_tab _ = SOME rows ==> _`,
            `!i rows. i < plen /\ FLOOKUP es_tab _ = SOME rows ==> _`,
            `!i rows. i < plen /\ FLOOKUP ks_tab _ = SOME rows ==> _`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disj1_tac >>
     `(a,e) <> (bpath,SUC d)` by
       (qpat_assum `!a e value. FLOOKUP blocks _ = _ ==> _` (drule_then ACCEPT_TAC)) >>
     `!r. r < plen ==> (a,e) <> (DROP (SUC r) bpath,FST (EL r bpath))` by
       (qpat_assum `~(?i. i < plen /\ (a,e) = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     qpat_assum `!a e. (a,e) <> (bpath,SUC d) /\ _ ==> FLOOKUP ms' _ = _ /\ _`
       (drule_all_then strip_assume_tac) >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`FLOOKUP ms' (a,e) = FLOOKUP ms_tab (a,e)`,
        `FLOOKUP es' (a,e) = FLOOKUP es_tab (a,e)`,
        `FLOOKUP ks' (a,e) = FLOOKUP ks_tab (a,e)`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* The single changed cell in each ancestor row is the live call index. *)
  `!i. i < plen ==>
     ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0.
       FLOOKUP acts (DROP (SUC i) bpath) =
         SOME (osf,otf,oi,oen,EL (SUC i) ords,ores,orest) /\
       LAST (EL (SUC i) ords) = FST (EL i bpath) /\
       FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) =
         SOME (eb,tb,eps,exs,eys,erho,ein,eh,SOME (ebe,ehbe),ecnt,OK eb0,F,NONE) /\
       EL i inds < LENGTH exs /\
       (EL (EL i inds) exs).inst_opcode = INVOKE /\
       (EL (EL i inds) exs).inst_id = SND (EL i bpath) /\
       eb0.vs_inst_idx = LENGTH eps + ecnt /\
       get_instruction tb eb0.vs_inst_idx = SOME (EL (EL i inds) exs) /\
       (if i = 0 then ~MEM (EL i inds) (TAKE ecnt erho) else
        ?k ch done child. k < LENGTH p /\ DROP (SUC i) bpath = DROP (SUC k) p /\
          (FST (EL i bpath), SND (EL i bpath)) = EL k p /\
          FLOOKUP calls (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath)) =
            SOME (EL i inds,ch,eb0,done,child,NONE))` by
    (rpt strip_tac >>
     `0 < SUC i /\ SUC i <= plen` by
       (qpat_assum `i < plen` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `!i. 0 < i /\ i <= plen ==> ?osf otf oi oen ores orest. _`
       (qspec_then `SUC i` (drule_all_then strip_assume_tac)) >>
     Cases_on `i`
     >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP acts (DROP (SUC 0) bpath) = SOME _`,
            `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
            `FLOOKUP blocks (p,d) = SOME _`, `LAST order = d`,
            `bpath = (d,inst.inst_id)::p`, `Abbrev (inds = _)`, `q < LENGTH xs`,
            `EL q xs = inst`, `inst.inst_opcode = INVOKE`, `s.vs_inst_idx = LENGTH ps + cnt`,
            `get_instruction bt s.vs_inst_idx = SOME inst`, `~MEM q (TAKE cnt sched)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL] >>
         rpt strip_tac >> gvs[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
     rename1 `SUC k < plen` >>
     `k < LENGTH p` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`SUC k < plen`,`plen = LENGTH bpath`,`bpath = (d,inst.inst_id)::p`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qpat_assum `!k. k < LENGTH p ==>
       ?sf tf inc entry order bb bt ps xs ys rho ini h0 be hbe count
        q h b0 done child cid e a. _`
       (qspec_then `k` (drule_then strip_assume_tac)) >>
     qpat_x_assum `(e,cid) = EL k p` (assume_tac o SYM) >>
     qpat_x_assum `a = DROP (SUC k) p` SUBST_ALL_TAC >>
     qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
       (drule_then strip_assume_tac) >>
     `EL (SUC k) inds = q'` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`Abbrev (inds = _)`,`k < LENGTH p`,`EL k p = (e,cid)`,
           `FLOOKUP calls (DROP (SUC k) p,e,cid) = SOME (q',_,_,_,_,NONE)`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL,EL_GENLIST]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts (DROP (SUC (SUC k)) bpath) = SOME _`,
        `FLOOKUP acts (DROP (SUC k) p) = SOME (_,_,_,_,order',NONE,NONE)`,
        `LAST order' = e`, `k < LENGTH p`, `EL k p = (e,cid)`,
        `bpath = (d,inst.inst_id)::p`, `EL (SUC k) inds = q'`,
        `FLOOKUP blocks (DROP (SUC k) p,e) = SOME (_,_,_,xs',_,_,_,_,_,_,OK b0,F,NONE)`,
        `FLOOKUP blocks (DROP (SUC k) p,e) = SOME (_,_,_,xs'',_,_,_,_,_,_,front,closed,brest)`,
        `FLOOKUP calls (DROP (SUC k) p,e,cid) = SOME (q',_,b0,_,_,NONE)`,
        `b0.vs_inst_idx = _`, `get_instruction bt' b0.vs_inst_idx = _`,
        `q' < LENGTH xs''`, `c = EL q' xs''`, `c.inst_id = cid`, `c.inst_opcode = INVOKE`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[EL] >> rpt strip_tac >> gvs[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!r. LIST_REL (\key slot. slot = ALOOKUP obs key)
     (FLAT (TAKE r ks)) (FLAT (TAKE r ms))` by
    (drule_all_then ACCEPT_TAC dft_packet_retained_prefix_lookup) >>
  `MEM root_tf C8.ctx_functions` by
    (qpat_assum `?nm lbl. C7.ctx_entry = SOME nm /\ _` strip_assume_tac >>
     drule_then ACCEPT_TAC venomInstTheory.lookup_function_MEM) >>
  `!ms_final. FLOOKUP ms' (p,d) = SOME ms_final ==>
     TAKE q ms_final = TAKE q ms` by
    (rpt strip_tac >>
     qpat_assum `!i rows. i < plen /\ FLOOKUP ms_tab _ = SOME rows ==> _`
       (qspec_then `0` mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP ms' (p,d) = SOME ms_final`, `FLOOKUP ms_tab (p,d) = SOME ms`,
        `bpath = (d,inst.inst_id)::p`, `plen = LENGTH bpath`, `Abbrev (inds = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL] >>
     rpt strip_tac >> gvs[dftPacketTableSpliceTheory.dft_packet_row_prefix_splice]) >>
  qspecl_then
    [`acts`,`blocks`,`calls`,`ms_tab`,`es_tab`,`ks_tab`,`acts'`,`blocks'`,`calls'`,
     `ms'`,`es'`,`ks'`,`N`,`C7`,`C8`,`root_tf`,`root_entry`,`j`,`p`,`d`,`inst`,`s`,
     `cnt`,`sched`,`q`,`bpath`,`sf`,`fn`,`inc`,`entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,
     `hin`,`h0`,`be`,`hbe`,`ms`,`ess`,`ks`,`obs`,`cs`,`csf`,`callee`,`cbb`,`cbt`,`cps`,
     `cxs`,`cys`,`crho`,`has_body`,`s1`,`cbe`,`cm`,`ce`,`ck`] mp_tac
    dftPacketCallReplayJoinTheory.dft_packet_call_replay_preservation >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (map_every qx_gen_tac [`a`,`e`] >> rpt gen_tac >> disch_tac >>
        qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
          FLOOKUP blocks (a,e) = _ ==> _`
          (qspecl_then [`a`,`e`] (drule_then strip_assume_tac)) >>
        `?mrow erow krow. FLOOKUP ms_tab (a,e) = SOME mrow /\
          FLOOKUP es_tab (a,e) = SOME erow /\ FLOOKUP ks_tab (a,e) = SOME krow` by
          (map_every (fn pat => qpat_assum pat mp_tac)
            [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
             `FDOM blocks = FDOM ks_tab`,`FLOOKUP blocks (a,e) = SOME _`] >>
           POP_ASSUM_LIST (K all_tac) >>
           metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
        rpt (goal_assum (drule_at Any)))) >>
     (conj_tac >-
       (map_every qx_gen_tac [`a`,`e`] >> rpt gen_tac >> disch_tac >>
        qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
          (qspecl_then [`a`,`e`] (drule_then strip_assume_tac)) >>
        goal_assum (drule_at Any))) >>
     (conj_tac >-
       (map_every qx_gen_tac [`a`,`e`,`rb`,`rt`,`rp`,`rx`,`ry`,`rr`,`ri`,`rh`,
          `rbe`,`rbh`,`rcnt`,`rf`,`rclosed`,`rest`,
          `owner`,`target`,`incoming`,`ent`,`ord`,`res`,`nrest`,`rm`,`re`,`rk`] >>
        disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
        qpat_assum `!a e value rm re rk. FLOOKUP blocks (a,e) = SOME value /\ _ ==> _`
          (qspecl_then [`a`,`e`] (drule_all_then strip_assume_tac))
        >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) =
          SOME (rb,rt,rp,rx,ry,rr,ri,rh,SOME (rbe,rbh),rcnt,rf,rclosed,rest)` by
          (qpat_assum `(a,e) = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
        Q_TAC (fn t => SUBGOAL_THEN t
          (qx_choose_then `caller` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
          `?caller.
           EL i inds < LENGTH rx /\ (EL (EL i inds) rx).inst_opcode = INVOKE /\
           caller.vs_inst_idx = LENGTH rp + rcnt /\
           get_instruction rt caller.vs_inst_idx = SOME (EL (EL i inds) rx) /\
           (a = p \/ ?k ch done child.
             k < LENGTH p /\ a = DROP (SUC k) p /\ (e,SND (EL i bpath)) = EL k p /\
             FLOOKUP calls (a,e,SND (EL i bpath)) = SOME (EL i inds,ch,caller,done,child,NONE))`
        >- (qpat_assum `!i. i < plen ==>
             ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _`
             (qspec_then `i` (drule_then mp_tac)) >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) = SOME _`,
              `(a,e) = _`, `bpath = (d,inst.inst_id)::p`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss] >> rpt strip_tac >>
           gvs[] >> qexists_tac `eb0` >> simp[] >>
           Cases_on `i = 0` >- gvs[EL] >> gvs[] >> metis_tac[EL]) >>
        disj2_tac >> qexistsl [`SND (EL i bpath)`,`EL i inds`,`caller`,`target`,`rt`,`ry`,`EL i ords`] >>
        qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME _ ==> _`
          (qspec_then `a` (drule_then strip_assume_tac)) >>
        qpat_x_assum `FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) = SOME _` kall_tac >>
        qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
          FLOOKUP blocks (a,e) = _ ==> _`
          (qspecl_then [`a`,`e`] (drule_then mp_tac)) >>
        qpat_assum `FLOOKUP acts a = SOME (owner,target,incoming,ent,ord,res,nrest)` SUBST1_TAC >>
        simp[NoAsms] >> strip_tac >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        (conj_tac >-
          (qpat_assum `caller.vs_inst_idx = LENGTH rp + rcnt` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        (conj_tac >-
          (map_every qx_gen_tac [`cid`,`cq`,`ch`,`cb`,`done`,`child`,`ret`] >> disch_tac >>
           qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
             (qspecl_then [`a`,`e`,`cid`] (drule_then mp_tac)) >>
           qpat_assum `FLOOKUP blocks (a,e) = SOME (rb,rt,rp,rx,ry,rr,ri,rh,SOME (rbe,rbh),rcnt,rf,rclosed,rest)` SUBST1_TAC >>
           POP_ASSUM_LIST (K all_tac) >> simp[] >>
           namedCases_on `ret` ["", "retv"] >- (simp[] >> metis_tac[]) >>
           PairCases_on `retv` >> simp[] >> metis_tac[])) >>
        qpat_assum `!i. i < plen ==> DROP i bpath = _`
          (qspec_then `i` (drule_then assume_tac)) >>
        qpat_assum `(a,e) = _` mp_tac >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP ms' (a,e) = SOME _`,`FLOOKUP es' (a,e) = SOME _`,`FLOOKUP ks' (a,e) = SOME _`,
           `DROP i bpath = _`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss])) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     map_every (fn pat => conj_tac >-
       qpat_assum pat (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (cm = _)`, `Abbrev (ce = _)`, `Abbrev (ck = _)`] >>
     (conj_tac >-
       (map_every qx_gen_tac [`a`,`e`] >> rpt gen_tac >>
        disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
        qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
          _ ==> LENGTH ms = LENGTH xs /\ _`
          (qspecl_then [`a`,`e`] (drule_all_then (drule_then ACCEPT_TAC o cj 2 o cj 7))))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb`
         (mp_tac o MATCH_MP venomExecProofsTheory.lookup_block_MEM) >> simp[])) >>
     `EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY inst_shape_ok bb.bb_instructions /\ dft_remaining_inv sf bb xs be` by
       (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
          FLOOKUP blocks (a,e) = _ ==> _`
          (qspecl_then [`p`,`d`] (drule_then mp_tac)) >>
        qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` SUBST1_TAC >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (disch_tac >> qpat_assum `q = EL cnt sched` (SUBST1_TAC o SYM) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
          _ ==> LENGTH ms = LENGTH xs /\ _`
          (qspecl_then [`p`,`d`] (drule_all_then (ACCEPT_TAC o cj 6))))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  `bpath <> [] /\ EL 0 ords = [SUC d]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`bpath = _::p`, `HD ords = [SUC d]`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[GSYM HD]) >>
  `LENGTH (FLAT cm) = LENGTH (FLAT ce) /\
   LENGTH (FLAT cm) = LENGTH (FLAT ck) /\ EVERY (\x. x = NONE) (FLAT cm)` by
    (map_every (fn pat => qpat_assum pat (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt (disch_then SUBST1_TAC) >>
     Cases_on `has_body` >> simp[EVERY_FLAT,EVERY_GENLIST,
       LENGTH_FLAT,listTheory.MAP_GENLIST,combinTheory.o_DEF,COND_RAND]) >>
  let
    fun apply_path theorem finish =
      qspecl_then [`bpath`,`inds`,`ords`,`SUC d`,`ms_tab`,`ms'`,`es_tab`,`es'`,
        `ks_tab`,`ks'`,`cm`,`ce`,`ck`] mp_tac theorem >>
      qpat_assum `plen = LENGTH bpath` (SUBST1_TAC o SYM) >>
      (impl_tac >-
        (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (qx_gen_tac `i` >> disch_tac >>
        qpat_assum `!i. i < plen ==> ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _`
          (qspec_then `i` (drule_then
            (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
        qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME _ ==> _`
          (qspec_then `DROP (SUC i) bpath` (drule_then strip_assume_tac)) >>
        (conj_tac >-
          (qpat_assum `EL (SUC i) ords = GENLIST _ _` SUBST1_TAC >>
           POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT_GENLIST])) >>
        (conj_tac >-
          (qpat_assum `LAST (EL (SUC i) ords) = _` (SUBST1_TAC o SYM) >>
           qpat_assum `EL (SUC i) ords <> []` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[MEM_LAST_NOT_NIL])) >>
        qpat_assum `!i. i < plen ==> ?m e k. FLOOKUP ms_tab _ = SOME m /\ _`
          (qspec_then `i` (drule_then strip_assume_tac)) >>
        map_every (fn pat => qpat_assum pat (qspec_then `i` (drule_all_then strip_assume_tac)))
          [`!i rows. i < plen /\ FLOOKUP ms_tab _ = SOME rows ==> _`,
           `!i rows. i < plen /\ FLOOKUP es_tab _ = SOME rows ==> _`,
           `!i rows. i < plen /\ FLOOKUP ks_tab _ = SOME rows ==> _`] >>
        rename1 `FLOOKUP ms_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME mrow` >>
        rename1 `FLOOKUP es_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME erow` >>
        rename1 `FLOOKUP ks_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME krow` >>
        qexistsl [`mrow`,`erow`,`krow`] >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        `0 < i /\ i <= plen <=> i <> 0` by
          (qpat_assum `i < plen` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
        qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
          _ ==> LENGTH ms = LENGTH xs /\ _`
          (qspecl_then [`DROP (SUC i) bpath`,`FST (EL i bpath)`]
            (drule_all_then
              (drule_then (qspec_then `EL i inds` (drule_then (mp_tac o cj 3))) o cj 1 o cj 7))) >>
        disch_then (drule_then assume_tac) >>
        `EL (EL i inds) mrow = (if i = 0 then [] else
            FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (DROP i bpath,f)))) (EL i ords))) /\
         EL (EL i inds) erow = (if i = 0 then [] else
            FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (DROP i bpath,f)))) (EL i ords))) /\
         EL (EL i inds) krow = (if i = 0 then [] else
            FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (DROP i bpath,f)))) (EL i ords)))` by
          (Cases_on `i = 0`
           >- (map_every (fn pat => qpat_assum pat mp_tac)
                [`case FLOOKUP calls _ of NONE => _ | SOME _ => _`,
                 `(EL (EL i inds) _).inst_id = SND (EL i bpath)`,
                 `FLOOKUP calls (p,d,inst.inst_id) = NONE`, `bpath = _::p`,`i = 0`] >>
               POP_ASSUM_LIST (K all_tac) >> simp[EL] >> rpt strip_tac >> gvs[]) >>
           `0 < i` by
             (qpat_assum `i <> 0` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
           `i <= plen` by
             (qpat_assum `i < plen` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
           qpat_assum `!i. 0 < i /\ i <= plen ==> ?osf otf oi oen ores orest. _`
             (qspec_then `i` (drule_all_then strip_assume_tac)) >>
           qpat_assum `!i. i < plen ==> DROP i bpath = _`
             (qspec_then `i` (drule_then assume_tac)) >>
           qpat_assum `if i = 0 then _ else _` (mp_tac o SRULE [NoAsms]) >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`case FLOOKUP calls _ of NONE => _ | SOME _ => _`,
              `(EL (EL i inds) _).inst_id = SND (EL i bpath)`,
              `FLOOKUP acts (DROP i bpath) = SOME _`,
              `DROP i bpath = _`, `i <> 0`, `AM = _`, `AE = _`, `AK = _`] >>
           POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     finish
       (map_every qx_gen_tac [`i`,`f`] >> disch_then (CONJUNCTS_THEN assume_tac) >>
        qpat_assum `!i. i < plen ==> ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _`
          (qspec_then `i` (drule_then
            (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
        qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME _ ==> _`
          (qspec_then `DROP (SUC i) bpath` (drule_then strip_assume_tac)) >>
        `(DROP (SUC i) bpath,f) IN FDOM blocks` by
          (qpat_assum `!e. MEM e (EL (SUC i) ords) <=> _`
             (qspec_then `f` (drule_then ACCEPT_TAC o iffLR))) >>
        `?rv. FLOOKUP blocks (DROP (SUC i) bpath,f) = SOME rv` by
          (rewrite_tac[GSYM venomExecProofsTheory.FDOM_FLOOKUP] >> first_assum ACCEPT_TAC) >>
        `?mr er kr. FLOOKUP ms_tab (DROP (SUC i) bpath,f) = SOME mr /\
           FLOOKUP es_tab (DROP (SUC i) bpath,f) = SOME er /\
           FLOOKUP ks_tab (DROP (SUC i) bpath,f) = SOME kr` by
          (map_every (fn pat => qpat_assum pat mp_tac)
            [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
             `FDOM blocks = FDOM ks_tab`,`(DROP (SUC i) bpath,f) IN FDOM blocks`] >>
           POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
           qexistsl [`ms_tab ' (DROP (SUC i) bpath,f)`, `es_tab ' (DROP (SUC i) bpath,f)`,
                     `ks_tab ' (DROP (SUC i) bpath,f)`] >>
           gvs[FLOOKUP_DEF]) >>
        PairCases_on `rv` >>
        qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
          FLOOKUP blocks (a,e) = _ ==> _`
          (qspecl_then [`DROP (SUC i) bpath`,`f`] (drule_then strip_assume_tac)) >>
        rename1 `FLOOKUP blocks (DROP (SUC i) bpath,f) =
          SOME (rbb,rbt,rps,rxs,rys,rsched,rin,rh,rbody,rcnt,rfront,rclosed,rrest)` >>
        Cases_on `rbody`
        >- (map_every (fn pat => qpat_assum pat mp_tac)
              [`case NONE of NONE => _ | SOME _ => _`,
               `FLOOKUP ms_tab (DROP (SUC i) bpath,f) = SOME mr`,
               `FLOOKUP es_tab (DROP (SUC i) bpath,f) = SOME er`,
               `FLOOKUP ks_tab (DROP (SUC i) bpath,f) = SOME kr`] >>
            POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
        rename1 `FLOOKUP blocks (DROP (SUC i) bpath,f) =
          SOME (rbb,rbt,rps,rxs,rys,rsched,rin,rh,SOME rbe,rcnt,rfront,rclosed,rrest)` >>
        PairCases_on `rbe` >>
        qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
          _ ==> LENGTH ms = LENGTH xs /\ _`
          (qspecl_then [`DROP (SUC i) bpath`,`f`] (drule_all_then strip_assume_tac)) >>
        qexistsl [`mr`,`er`,`kr`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`LENGTH er = LENGTH mr`,`LENGTH kr = LENGTH mr`] >> simp[NoAsms] >>
        rpt strip_tac >> first_assum ACCEPT_TAC)))
  in
    apply_path dftPacketCallPathInsertionTheory.dft_packet_call_path_insertion_at_level I >>
    disch_then (mk_asm "call insertion at level") >>
    apply_path dftPacketCallRootConservationTheory.dft_packet_call_root_conservation
      (fn rows => (conj_tac >- rows) >> first_assum ACCEPT_TAC) >>
    disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  end >>
  qpat_assum `?order. FLOOKUP acts [] = _`
    (qx_choose_then `root_order` assume_tac) >>
  `EL plen ords = root_order` by
    (qpat_assum `!i. 0 < i /\ i <= plen ==> ?osf otf oi oen ores orest. _`
       (qspec_then `plen` mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,root_order,NONE,NONE)`,
        `plen = LENGTH bpath`,`bpath <> []`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[DROP_LENGTH_NIL, LENGTH_NIL] >>
     rpt disch_tac >>
     `0 < LENGTH bpath` by (Cases_on `bpath` >> gvs[]) >> metis_tac[]) >>
  mp_tac (Q.SPECL [`acts`,`ks_tab`,`p`,`d`,`inst`,`bpath`,`cxs`]
    dftPacketCallKeyFreshnessTheory.dft_packet_call_key_freshness) >>
  (impl_tac >-
   (reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`MEM (c,e,cid) _`, `FLOOKUP acts a = SOME _`,
       `!a e. (a,e) IN FDOM blocks ==> a IN FDOM acts`] >>
    qhdtm_assum `dft_focus_packet_rel` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
    drule_all dft_packet_retained_key_origin >> strip_tac >>
    ` (c,e) IN FDOM blocks` by
      (rewrite_tac[venomExecProofsTheory.FDOM_FLOOKUP] >> goal_assum (drule_at Any)) >>
    first_assum (drule_then ACCEPT_TAC))) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ALL_DISTINCT (FLAT ck)` by
    (qpat_assum `ALL_DISTINCT (FLAT (MAP _ cxs))` mp_tac >>
     qpat_assum `Abbrev (ck = _)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `has_body` >> simp[markerTheory.Abbrev_def, GSYM GENLIST_EL_MAP]) >>
  `!a sf tf inc entry order res rest key.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\ MEM key (FLAT ck) ==>
    ~MEM key (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) order))` by
    (qpat_assum `!a sf tf inc entry order res rest key. _ /\ MEM key (FLAT (MAP _ cxs)) ==> _`
       mp_tac >> qpat_assum `Abbrev (ck = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `has_body` >>
     simp[markerTheory.Abbrev_def, GSYM GENLIST_EL_MAP]) >>
  `FLOOKUP acts' [] = SOME (root_sf,root_tf,0,root_entry,root_order,NONE,NONE)` by
    first_assum (drule_then ACCEPT_TAC) >>
  qabbrev_tac `AM1 = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms' (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a)))))))))` >>
  qabbrev_tac `AE1 = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es' (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a)))))))))` >>
  qabbrev_tac `AK1 = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks' (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a)))))))))` >>
  let
    fun root_norm def lookup =
      map_every (fn pat => qpat_assum pat mp_tac)
        [def,lookup,`EL plen ords = root_order`] >>
      POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]
  in
    `AM1 [] = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' ([],f)))) (EL plen ords))` by
      root_norm `Abbrev (AM1 = _)` `FLOOKUP acts' [] = _` >>
    `AE1 [] = FLAT (MAP (\f. FLAT (THE (FLOOKUP es' ([],f)))) (EL plen ords))` by
      root_norm `Abbrev (AE1 = _)` `FLOOKUP acts' [] = _` >>
    `AK1 [] = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' ([],f)))) (EL plen ords))` by
      root_norm `Abbrev (AK1 = _)` `FLOOKUP acts' [] = _` >>
    `AM [] = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab ([],f)))) (EL plen ords))` by
      root_norm `AM = _` `FLOOKUP acts [] = _` >>
    `AK [] = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab ([],f)))) (EL plen ords))` by
      root_norm `AK = _` `FLOOKUP acts [] = _`
  end >>
  let
    fun root_transfer facts =
      map_every (fn pat => qpat_assum pat mp_tac)
        (facts @ [`AM1 [] = _`,`AE1 [] = _`,`AK1 [] = _`,
                  `AM [] = _`,`AK [] = _`]) >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> metis_tac[]
  in
    `LENGTH (AM1 []) = LENGTH (AE1 [])` by root_transfer
      [`LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' ([],f)))) (EL plen ords))) =
        LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP es' ([],f)))) (EL plen ords)))`] >>
    `LENGTH (AM1 []) = LENGTH (AK1 [])` by root_transfer
      [`LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' ([],f)))) (EL plen ords))) =
        LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' ([],f)))) (EL plen ords)))`] >>
    `MAP THE (FILTER IS_SOME (AM1 [])) = MAP THE (FILTER IS_SOME (AM []))` by
      root_transfer [`MAP THE (FILTER IS_SOME (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' ([],f))))
        (EL plen ords)))) = _`] >>
    `PERM (MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK1 [],AM1 [])))) obs` by
      root_transfer [`MAP (\(key,slot). (key,THE slot)) (FILTER _ (ZIP (_, _))) = _`,
                     `PERM (MAP (\(key,slot). (key,THE slot)) (FILTER _ (ZIP (AK [],AM [])))) obs`] >>
    `!key. MEM key (FLAT ck) ==> ~MEM key (AK [])` by
      (qpat_assum `!a sf tf inc entry order res rest key. _ /\ MEM key (FLAT ck) ==> _`
         (qspec_then `[]` mp_tac) >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,root_order,NONE,NONE)`,
          `AK [] = _`,`EL plen ords = root_order`] >>
       POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> metis_tac[]) >>
    `ALL_DISTINCT (AK1 [])` by
      root_transfer [`ALL_DISTINCT (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab ([],f))))
        (EL plen ords))) /\ _ ==> _`, `ALL_DISTINCT (AK [])`, `ALL_DISTINCT (FLAT ck)`,
        `!key. MEM key (FLAT ck) ==> ~MEM key (AK [])`]
  end >>
  `trace_gas (TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry)) = obs` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) = _`,
       `obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry))`,
       `EL j (trace_blocks [] 0 N C8 root_tf root_entry) = _`,
       `j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`, `inst.inst_opcode = INVOKE`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     simp[TAKE_SUC_BY_TAKE, SNOC_APPEND, dftGasFromListReadingsTheory.trace_gas_append,
          trace_gas_def, visit_gas_def]) >>
  `s1.vs_gas_readings = s.vs_gas_readings` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`setup_callee callee args s = SOME cs`,`enters_block callee cs s1`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gasOracleReplayTheory.gas_setup_callee_readings,
       concretizeLayoutCutSafeTheory.enters_block_readings]) >>
  `!va ve cid.
     (!i. i < plen ==> (va,ve,cid) <>
       (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath))) ==>
     FLOOKUP calls' (va,ve,cid) = FLOOKUP calls (va,ve,cid) /\
     AM1 ((ve,cid)::va) = AM ((ve,cid)::va) /\
     AE1 ((ve,cid)::va) = AE ((ve,cid)::va) /\
     AK1 ((ve,cid)::va) = AK ((ve,cid)::va)` by
    (rpt gen_tac >> disch_tac >>
     `0 < plen` by
       (qpat_assum `plen = LENGTH bpath` SUBST1_TAC >>
        qpat_assum `bpath = _::p` SUBST1_TAC >> simp[]) >>
     `(va,ve,cid) <> (p,d,inst.inst_id)` by
       (qpat_assum `!i. i < plen ==> (va,ve,cid) <> _`
          (qspec_then `0` (drule_then mp_tac)) >>
        qpat_assum `bpath = _::p` SUBST1_TAC >> simp[NoAsms]) >>
     conj_tac >- first_assum (drule_then ACCEPT_TAC) >>
     `!i. i <= plen ==> (ve,cid)::va <> DROP i bpath` by
       (Cases >> strip_tac
        >- (qpat_assum `bpath = _::p` SUBST1_TAC >>
            qpat_assum `(va,ve,cid) <> (p,d,inst.inst_id)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ] >> metis_tac[]) >>
        rename1 `SUC n <= plen` >>
        Cases_on `SUC n = plen`
        >- (qpat_assum `plen = LENGTH bpath` mp_tac >>
            qpat_assum `SUC n = plen` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[]) >>
        `SUC n < plen` by
          (qpat_assum `SUC n <= plen` mp_tac >> qpat_assum `SUC n <> plen` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
        qpat_assum `!i. i < plen ==> DROP i bpath = _`
          (qspec_then `SUC n` (drule_then SUBST1_TAC)) >>
        qpat_assum `!i. i < plen ==> (va,ve,cid) <> _`
          (qspec_then `SUC n` (drule_then mp_tac)) >>
        POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ] >> metis_tac[]) >>
     `((ve,cid)::va) <> bpath` by
       (qpat_assum `!i. i <= plen ==> (ve,cid)::va <> _` (qspec_then `0` mp_tac) >> simp[NoAsms]) >>
     `FLOOKUP acts' ((ve,cid)::va) = FLOOKUP acts ((ve,cid)::va)` by
       first_assum (drule_then ACCEPT_TAC) >>
     `!e. FLOOKUP ms' ((ve,cid)::va,e) = FLOOKUP ms_tab ((ve,cid)::va,e) /\
          FLOOKUP es' ((ve,cid)::va,e) = FLOOKUP es_tab ((ve,cid)::va,e) /\
          FLOOKUP ks' ((ve,cid)::va,e) = FLOOKUP ks_tab ((ve,cid)::va,e)` by
       (gen_tac >>
        qpat_assum `!a e. (a,e) <> (bpath,SUC d) /\ _ ==> FLOOKUP ms' (a,e) = _ /\ _`
          (qspecl_then [`(ve,cid)::va`,`e`] irule) >>
        reverse conj_tac
        >- (qpat_assum `(ve,cid)::va <> bpath` mp_tac >> simp[NoAsms,pairTheory.PAIR_EQ]) >>
        qx_gen_tac `r` >> disch_tac >>
        `SUC r <= plen` by
          (qpat_assum `r < plen` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
        qpat_assum `!i. i <= plen ==> (ve,cid)::va <> _`
          (qspec_then `SUC r` (drule_then mp_tac)) >> simp[NoAsms,pairTheory.PAIR_EQ]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (AM1 = _)`,`Abbrev (AE1 = _)`,`Abbrev (AK1 = _)`,
        `AM = _`,`AE = _`,`AK = _`,
        `FLOOKUP acts' ((ve,cid)::va) = _`,
        `!e. FLOOKUP ms' ((ve,cid)::va,e) = _ /\ _`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
  suspend "call_packet_assembly"
QED
Resume dft_focus_packet_step_retained[call_packet_assembly]:
  qexistsl [`N'`,`obs`,`acts'`,`blocks'`,`calls'`,`ms'`,`es'`,`ks'`,
            `bpath`,`SUC d`,`AM1 []`,`AE1 []`,`s1.vs_gas_readings`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (once_rewrite_tac [CONJ_ASSOC] >> reverse conj_tac
      >- (map_every qx_gen_tac [`path0`,`depth0`,`id0`,`ix0`,`at0`,`b0'`,`done0`,`ent0`,`ret0`] >>
          strip_tac >> qexists_tac `ret0` >>
          Cases_on `(path0,depth0,id0) = (p,d,inst.inst_id)`
          >- (map_every (fn pat => qpat_assum pat mp_tac)
                [`FLOOKUP calls (path0,depth0,id0) = _`,
                 `(path0,depth0,id0) = (p,d,inst.inst_id)`,
                 `FLOOKUP calls (p,d,inst.inst_id) = NONE`] >>
              POP_ASSUM_LIST (K all_tac) >> simp[]) >>
          (conj_tac
           >- (qpat_assum `!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls' key = FLOOKUP calls key`
                 (drule_then (fn th => pure_rewrite_tac[th])) >>
               first_assum ACCEPT_TAC) >>
           simp[])) >>
      map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH (AM1 []) = LENGTH (AE1 [])`,
        `MAP THE (FILTER IS_SOME (AM1 [])) = MAP THE (FILTER IS_SOME (AM []))`,
        `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0)`,
        `s1.vs_gas_readings = s.vs_gas_readings`,`raw_slots = AM []`,
        `unused = s.vs_gas_readings`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  pure_rewrite_tac [dft_focus_packet_rel_def] >>
  qexistsl [`SUC j`,`obs`,`AM1`,`AE1`,`AK1`,`row_eval`,`plan_eval`,`call_setup`,
    `plan_ok`,`levels_ok`,
    `<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|> :: stk`,
    `MAP (op_prov G) ops`,`FEMPTY`,`tn with t_var := FEMPTY`,`callee`,`inst'`,`s1`,
    `om::oms`,`FEMPTY`,`h::hs`,
    `[OriginCallee cs; OriginObserve
       (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY inst' s1)]`] >>
  rpt (FIRST [first_assum ACCEPT_TAC, REFL_TAC, conj_tac])
  >- (qpat_assum `plen = LENGTH bpath` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `plen = LENGTH bpath` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
  >- first_assum (ACCEPT_TAC o SYM)
  >- (qpat_assum `Abbrev (AM1 = _)` mp_tac >> simp[NoAsms,markerTheory.Abbrev_def])
  >- (qpat_assum `Abbrev (AE1 = _)` mp_tac >> simp[NoAsms,markerTheory.Abbrev_def])
  >- (qpat_assum `Abbrev (AK1 = _)` mp_tac >> simp[NoAsms,markerTheory.Abbrev_def])
  >- (qpat_assum `s1.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`FDOM blocks' = _`,`FDOM ms' = _`,`FDOM blocks = FDOM ms_tab`] >> simp[NoAsms])
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`FDOM blocks' = _`,`FDOM es' = _`,`FDOM blocks = FDOM es_tab`] >> simp[NoAsms])
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`FDOM blocks' = _`,`FDOM ks' = _`,`FDOM blocks = FDOM ks_tab`] >> simp[NoAsms])
  >- (qexists `root_order` >> first_assum ACCEPT_TAC)
  >- (qpat_assum `plen = LENGTH bpath` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
  >- suspend "call_block_records"
  >- (qexistsl [`csf`,`d`,`cs`,`[SUC d]`,`cbb`,`cbt`,`cps`,`cxs`,`cys`,
                 `crho`,`cs`,`SUC j`,`cbe`,`0`] >> simp[NoAsms] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      (conj_tac >-
        (drule_then (SUBST1_TAC o CONJUNCT1) frameCfgBoundaryTheory.enters_block_control_labels >>
         first_assum ACCEPT_TAC)) >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `case cbe of NONE => _ | SOME _ => _` mp_tac >>
      namedCases_on `cbe` ["", "cursor_body"]
      >- (simp[NoAsms] >> disch_then strip_assume_tac >>
          qpat_assum `eval_phis cs cbt.bb_instructions = OK sp` (fn th => simp[NoAsms,th]) >>
          conj_tac >- first_assum ACCEPT_TAC >> first_assum MATCH_ACCEPT_TAC) >>
      PairCases_on `cursor_body` >> simp[NoAsms,EL] >> disch_then strip_assume_tac >>
      `0 < LENGTH cys` by
        (qpat_assum `cys <> []` mp_tac >> Cases_on `cys` >> simp[NoAsms]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- suspend "call_records"
  >- (qpat_assum `plen = LENGTH bpath` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
  >- suspend "call_row_replay"
  >- (map_every qx_gen_tac [`va`,`ve`,`cid`] >> rpt gen_tac >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      map_every qx_gen_tac [`fuel`,`kgss`,`tail`,`u`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      `N <= fuel` by
        (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
      qpat_assum `!a e id cq ch cb done child ret rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm.
        FLOOKUP calls' (a,e,id) = _ /\ _ ==> _`
        (qspecl_then [`va`,`ve`,`cid`] (drule_all_then ACCEPT_TAC)))
  >- (map_every qx_gen_tac [`va`,`ve`,`owner`,`target`,`incoming`,`ent`,`ord`,`res`,`nrest`,
         `vb`,`vt`,`vp`,`vx`,`vy`,`vr`,`vi`,`vh`,`vbe`,`vbh`,`vc`,`vf`,`vu`,`vm`,`ves`,`vk`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      `(va,ve) <> (bpath,SUC d)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP blocks' (va,ve) = SOME _`,
            `FLOOKUP blocks' (bpath,SUC d) = SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
      `FLOOKUP blocks (va,ve) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,SOME(vbe,vbh),vc,vf,T,SOME vu)` by
        (qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
           (qspecl_then [`va`,`ve`] (drule_then (SUBST1_TAC o SYM))) >> first_assum ACCEPT_TAC) >>
      `va <> bpath` by
        (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
            FLOOKUP blocks (a,e) = _ ==> _`
            (qspecl_then [`va`,`ve`] (drule_then strip_assume_tac)) >>
         qpat_assum `FLOOKUP acts bpath = NONE` mp_tac >>
         qpat_assum `FLOOKUP acts va = SOME _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
      `FLOOKUP acts va = SOME (owner,target,incoming,ent,ord,res,nrest)` by
        (qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = _`
           (drule_then (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
      `!i. i < plen ==> (va,ve) <> (DROP (SUC i) bpath,FST (EL i bpath))` by
        (qx_gen_tac `i` >> disch_tac >>
         qpat_assum `!i. i < plen ==> ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _`
           (qspec_then `i` (drule_then strip_assume_tac)) >>
         qpat_assum `FLOOKUP blocks (va,ve) = SOME _` mp_tac >>
         qpat_assum `FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) = SOME _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
      qpat_assum `!a e. (a,e) <> (bpath,SUC d) /\ _ ==> FLOOKUP ms' (a,e) = _ /\ _`
        (qspecl_then [`va`,`ve`] (drule_all_then strip_assume_tac)) >>
      map_every (fn (frame,query) =>
        qpat_assum frame (fn th => qpat_assum query (assume_tac o REWRITE_RULE [th])))
        [(`FLOOKUP ms' (va,ve) = FLOOKUP ms_tab (va,ve)`, `FLOOKUP ms' (va,ve) = SOME vm`),
         (`FLOOKUP es' (va,ve) = FLOOKUP es_tab (va,ve)`, `FLOOKUP es' (va,ve) = SOME ves`),
         (`FLOOKUP ks' (va,ve) = FLOOKUP ks_tab (va,ve)`, `FLOOKUP ks' (va,ve) = SOME vk`)] >>
      qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
         FLOOKUP acts a = SOME _ /\ FLOOKUP blocks (a,e) = SOME _ /\ _ ==> _`
        (qspecl_then [`va`,`ve`] (drule_all_then strip_assume_tac)) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qx_gen_tac `fuel` >> disch_tac >>
      `N <= fuel` by
        (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
      first_assum (drule_then ACCEPT_TAC))
  >- (map_every qx_gen_tac [`va`,`owner`,`target`,`incoming`,`ent`,`ord`,`vr`,`vu`] >> disch_tac >>
      `!i. i <= plen ==> va <> DROP i bpath` by
        (qpat_assum `!a sf tf inc entry order res rest. FLOOKUP acts' a = SOME _ ==> _`
           (qspec_then `va` (drule_then mp_tac)) >>
         POP_ASSUM_LIST (K all_tac) >> simp[MEM_GENLIST, GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC] >> metis_tac[]) >>
      `va <> bpath` by
        (qpat_assum `!i. i <= plen ==> va <> _` (qspec_then `0` mp_tac) >> simp[NoAsms]) >>
      `FLOOKUP acts va = SOME (owner,target,incoming,ent,ord,SOME vr,SOME vu)` by
        (qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = _`
           (drule_then (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
      `!e. FLOOKUP ms' (va,e) = FLOOKUP ms_tab (va,e) /\
           FLOOKUP es' (va,e) = FLOOKUP es_tab (va,e) /\
           FLOOKUP ks' (va,e) = FLOOKUP ks_tab (va,e)` by
        (gen_tac >>
         qpat_assum `!a e. (a,e) <> (bpath,SUC d) /\ _ ==> FLOOKUP ms' (a,e) = _ /\ _`
           (qspecl_then [`va`,`e`] irule) >>
         reverse conj_tac
         >- (qpat_assum `va <> bpath` mp_tac >> simp[NoAsms,pairTheory.PAIR_EQ]) >>
         qx_gen_tac `r` >> disch_tac >>
         `SUC r <= plen` by
           (qpat_assum `r < plen` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
         qpat_assum `!i. i <= plen ==> va <> _`
           (qspec_then `SUC r` (drule_then mp_tac)) >> simp[NoAsms,pairTheory.PAIR_EQ]) >>
      `AM1 va = AM va /\ AE1 va = AE va /\ AK1 va = AK va` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`Abbrev (AM1 = _)`,`Abbrev (AE1 = _)`,`Abbrev (AK1 = _)`,
           `AM = _`,`AE = _`,`AK = _`,
           `FLOOKUP acts' va = _`,`FLOOKUP acts va = _`,
           `!e. FLOOKUP ms' (va,e) = _ /\ _`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
      map_every (fn pat => qpat_assum pat SUBST1_TAC)
        [`AM1 va = AM va`,`AE1 va = AE va`,`AK1 va = AK va`] >>
      qpat_assum `!a sf tf inc entry order r8 u0.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _`
        (qspec_then `va` (drule_then strip_assume_tac)) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qx_gen_tac `fuel` >> disch_tac >>
      `N <= fuel` by
        (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
      first_assum (drule_then ACCEPT_TAC))
  >- (map_every qx_gen_tac [`va`,`ve`] >> rpt gen_tac >> disch_tac >>
      Cases_on `(va,ve) = (bpath,SUC d)`
      >- (map_every (fn pat => qpat_assum pat mp_tac)
            [`FLOOKUP blocks' (va,ve) = SOME _`,
             `FLOOKUP blocks' (bpath,SUC d) = SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`,
             `(va,ve) = (bpath,SUC d)`] >>
          POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
      qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
        (qspecl_then [`va`,`ve`] (drule_then (fn th =>
          qpat_assum `FLOOKUP blocks' (va,ve) = SOME _` (assume_tac o REWRITE_RULE [th])))) >>
      qx_gen_tac `r` >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
           FLOOKUP blocks (a,e) = _ ==> !q. _ ==> ?h b0 done child ir child_out caller_post.
             FLOOKUP calls _ = _`
        (qspecl_then [`va`,`ve`] (drule_then (qspec_then `r` (drule_all_then strip_assume_tac)))) >>
      qpat_assum `!key value. FLOOKUP calls key = SOME value ==> _` (drule_then assume_tac) >>
      rpt (goal_assum (drule_at Any)))
  >- (map_every qx_gen_tac [`vb`,`vt`,`vp`,`vx`,`vy`,`vr`,`vi`,`vh`,
        `vbe`,`vbh`,`vc`,`vsf`,`vinc`,`vent`,`vord`] >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_assum `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`
        (fn th => qpat_x_assum `FLOOKUP acts' bpath = SOME (vsf,callee,vinc,vent,vord,NONE,NONE)`
          (strip_assume_tac o SRULE [th])) >>
      qpat_assum `FLOOKUP blocks' (bpath,SUC d) = SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`
        (fn th => qpat_x_assum `FLOOKUP blocks' (bpath,SUC d) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,SOME (vbe,vbh),vc,OK s1,F,NONE)`
          (strip_assume_tac o SRULE [th])) >>
      map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC o SYM))
        [`cxs = vx`,`crho = vr`] >>
      qpat_assum `vc = 0` SUBST_ALL_TAC >>
      `has_body` by
        (qpat_assum `cbe = SOME (vbe,vbh)` mp_tac >>
         qpat_assum `cbe = if has_body then _ else _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `has_body` >> simp[]) >>
      qpat_assum `has_body` (fn body =>
        qpat_assum `cbe = if has_body then _ else _` (fn eq =>
          qpat_assum `case cbe of NONE => _ | SOME _ => _`
            (strip_assume_tac o SRULE [eq,body]))) >>
      `EL 0 cys = inst' /\ 0 < LENGTH cys` by
        (qpat_assum `inst' = HD cys` mp_tac >> qpat_assum `cys <> []` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `cys` >> simp[]) >>
      `from_block [EL (EL 0 crho) cxs] inst'` by
        (qpat_assum `LIST_REL _ crho cys` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
         qpat_assum `EL 0 cys = inst'` mp_tac >>
         qpat_assum `0 < LENGTH cys` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         metis_tac[]) >>
      `EL (EL 0 crho) cxs = inst'` by
        (drule_all dftGasInvMemoryObservationTheory.inv_memory_observation_original >> simp[MEM]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `lookup_block cbb.bb_label csf.fn_blocks = SOME cbb /\
       lookup_block cbb.bb_label callee.fn_blocks = SOME cbt` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`cbb.bb_label = cs.vs_current_bb`, `lookup_block cs.vs_current_bb csf.fn_blocks = SOME cbb`,
            `lookup_block cs.vs_current_bb callee.fn_blocks = SOME cbt`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[]) >>
      irule dft_packet_memory_schedule_predecessors >>
      qpat_assum `dft_fn_rel csf callee` (irule_at Any) >>
      rpt (first_assum (irule_at Any)) >> simp[] >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`inv_memory_observation inst'.inst_opcode`,`inst' = HD cys`,`cys = vy`] >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  suspend "call_rooted_cuts"
QED
Resume dft_focus_packet_step_retained[call_rooted_cuts]:
  `!i. i < plen ==>
     ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0 rm re rk.
       FLOOKUP acts (DROP (SUC i) bpath) =
         SOME (osf,otf,oi,oen,EL (SUC i) ords,ores,orest) /\
       LAST (EL (SUC i) ords) = FST (EL i bpath) /\
       FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) =
         SOME (eb,tb,eps,exs,eys,erho,ein,eh,SOME (ebe,ehbe),ecnt,OK eb0,F,NONE) /\
       FLOOKUP ms_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME rm /\
       FLOOKUP es_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME re /\
       FLOOKUP ks_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME rk /\
       LENGTH rm = LENGTH exs /\ LENGTH re = LENGTH exs /\ LENGTH rk = LENGTH exs /\
       EL i inds < LENGTH exs /\
       (EL (EL i inds) exs).inst_opcode = INVOKE /\
       (EL (EL i inds) exs).inst_id = SND (EL i bpath) /\
       (if i = 0 then ~MEM (EL i inds) (TAKE ecnt erho) else
         ?h b0 done child.
           FLOOKUP calls (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath)) =
             SOME (EL i inds,h,b0,done,child,NONE)) /\
       (!r. r < LENGTH exs /\ MEM r (TAKE ecnt erho) /\
         (EL r exs).inst_opcode = INVOKE ==>
         ?q h b0 done child ir out post.
           FLOOKUP calls (DROP (SUC i) bpath,FST (EL i bpath),(EL r exs).inst_id) =
             SOME (q,h,b0,done,child,SOME (ir,out,post)))` by
    (rpt strip_tac >>
     let val actrow = [`osf`,`otf`,`oi`,`oen`,`ores`,`orest`,`eb`,`tb`,`eps`,`exs`,`eys`,
                       `erho`,`ein`,`eh`,`ebe`,`ehbe`,`ecnt`,`eb0`]
         val cells = [`hist_ms`,`hist_es`,`hist_ks`]
         fun obtain pat qs = qpat_assum pat (qspec_then `i` (drule_then
           (List.foldr (fn (q,k) => qx_choose_then q k)
             (REPEAT_TCL CONJUNCTS_THEN assume_tac) qs)))
     in
       obtain `!i. i < plen ==> ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _` actrow >>
       obtain `!i. i < plen ==> ?m e k.
          FLOOKUP ms_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME m /\ _` cells >>
       qexistsl (actrow @ cells)
     end >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
         _ ==> LENGTH ms = LENGTH xs /\ _`
       (qspecl_then [`DROP (SUC i) bpath`,`FST (EL i bpath)`]
         (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     `LENGTH hist_es = LENGTH exs /\ LENGTH hist_ks = LENGTH exs` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`LENGTH hist_ms = LENGTH exs`,`LENGTH hist_es = LENGTH hist_ms`,
           `LENGTH hist_ks = LENGTH hist_ms`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
     >- (qpat_assum `if i = 0 then _ else _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `i = 0` >> simp[] >> metis_tac[]) >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> !q. _ ==> ?h b0 done child ir out post. _`
       (qspecl_then [`DROP (SUC i) bpath`,`FST (EL i bpath)`]
         (drule_then mp_tac)) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  map_every qx_gen_tac [`va`,`ve`,`vsf`,`vtf`,`vinc`,`vent`,`vord`,`vres`,`vrest`,
    `vb`,`vt`,`vp`,`vx`,`vy`,`vr`,`vi`,`vh`,`vbody`,`vc`,`vf`,`vclosed`,`vbr`,
    `vq`,`vz`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  reverse (Cases_on `(va,ve) = (bpath,SUC d)`)
  >- suspend "call_historical_cut" >>
  suspend "call_fresh_cut"
QED
Resume dft_focus_packet_step_retained[call_fresh_cut]:
  qpat_x_assum `(va,ve) = (bpath,SUC d)`
    (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS o SRULE []) >>
  qpat_assum `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`
    (fn row => qpat_x_assum `FLOOKUP acts' bpath = SOME (vsf,vtf,vinc,vent,vord,vres,vrest)`
      (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o
       PURE_REWRITE_RULE [row,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  qpat_assum `FLOOKUP blocks' (bpath,SUC d) =
      SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`
    (fn row => qpat_x_assum `FLOOKUP blocks' (bpath,SUC d) =
      SOME (vb,vt,vp,vx,vy,vr,vi,vh,vbody,vc,vf,vclosed,vbr)`
      (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o
       PURE_REWRITE_RULE [row,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  qabbrev_tac `call_z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
       body_entry count front closed brest q z.
     FLOOKUP acts a = _ /\ FLOOKUP blocks (a,e) = _ /\ _ ==>
     ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (qspecl_then [`p`,`d`] (mp_tac o
      ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] o ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`q`,`call_z`] mp_tac) >>
  (impl_tac >- (disj1_tac >> simp[NoAsms,Abbr `call_z`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  let val witnesses = [`old_cuts`,`old_levels`,`M0`,`E0`,`K0`,`mr0`,`er0`,`kr0`]
  in disch_then (List.foldr (fn (q,k) => qx_choose_then q k)
       (MAP_EVERY assume_tac o CONJUNCTS) witnesses)
  end >>
  `old_cuts <> [] /\ old_levels <> []` by
    (qpat_assum `MAP _ old_cuts = REVERSE _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_assum `LENGTH old_cuts = LENGTH old_levels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `old_cuts` >> Cases_on `old_levels` >> simp[]) >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> _`
       (qspecl_then [`p`,`d`] (drule_then mp_tac)) >>
     qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `inst = EL (LENGTH call_z)
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (qpat_assum `EL q xs = inst` (SUBST1_TAC o SYM) >> sym_tac >>
     irule dft_packet_cut_instruction >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `ps` >>
     simp[Abbr `call_z`]) >>
  `?past ds pre plan.
      old_cuts = past ++ [(p,ds,d,q,call_z)] /\
      old_levels = pre ++ [(sf,plan,NONE)] /\
      plan = MAP (\f. case THE (FLOOKUP blocks (p,f)) of
        (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
          (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++
        [(bb,d,call_z)] /\ LAST plan = (bb,d,call_z)` by
    (`?past row. old_cuts = past ++ [row]` by
       (qexistsl [`FRONT old_cuts`,`LAST old_cuts`] >>
        sym_tac >> irule APPEND_FRONT_LAST >> first_assum ACCEPT_TAC) >>
     PairCases_on `row` >>
     `LENGTH past < LENGTH old_cuts /\ SUC (LENGTH past) = LENGTH old_cuts /\
       EL (LENGTH past) old_cuts = (row0,row1,row2,row3,row4)` by
       (qpat_assum `old_cuts = past ++ _` (fn th => simp[NoAsms,th,EL_APPEND2])) >>
     qpat_assum `!i ai ds ei qi zi. i < LENGTH old_cuts /\ EL i old_cuts = _ ==>
         ?sfi tfi inci enti orderi resi nresti
          bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
       (drule_all_then (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS))) >>
     qpat_assum `SUC (LENGTH past) = LENGTH old_cuts` (fn last =>
       qpat_x_assum `if SUC (LENGTH past) = LENGTH old_cuts then _ else _`
         (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS o REWRITE_RULE[last])) >>
     qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (fn a =>
       qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,OK s,F,NONE)` (fn b =>
         qpat_x_assum `FLOOKUP acts p = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)`
           (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o
             PURE_REWRITE_RULE [a,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
         qpat_x_assum `FLOOKUP blocks (p,d) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti)`
           (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o
             PURE_REWRITE_RULE [b,optionTheory.SOME_11,pairTheory.PAIR_EQ]))) >>
     `?pre level. old_levels = pre ++ [level]` by
       (qexistsl [`FRONT old_levels`,`LAST old_levels`] >>
        sym_tac >> irule APPEND_FRONT_LAST >> first_assum ACCEPT_TAC) >>
     `LENGTH pre = LENGTH past` by
       (qpat_assum `LENGTH old_cuts = LENGTH old_levels` mp_tac >>
        map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
          [`old_cuts = past ++ _`,`old_levels = pre ++ _`] >>
        simp[NoAsms]) >>
     qpat_x_assum `EL (LENGTH past) old_levels = _` mp_tac >>
     map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
       [`old_levels = pre ++ _`,`SUC (LENGTH past) = LENGTH old_cuts`] >>
     qpat_assum `LENGTH pre = LENGTH past` (fn th => rewrite_tac[GSYM th]) >>
     simp[NoAsms,EL_APPEND2] >> disch_then SUBST_ALL_TAC >>
     qexistsl [`past`,`row1`] >>
     (conj_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  rename1 `old_cuts = past ++ [(p,caller_rows,d,q,call_z)]` >>
  qabbrev_tac `incoming0 = MAP (\(ai,ds,ei,qi,zi).
      case THE (FLOOKUP acts ai) of
        (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) old_cuts` >>
  `!fuel gs tail events0 u.
    N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
    rooted_eval fuel C7 old_levels (root_entry with vs_gas_readings := gs ++ tail) = (events0,OK u) ==>
    (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
    (!callee argv. setup_callee callee argv (u with vs_gas_readings := s.vs_gas_readings) =
      setup_callee callee argv s)` by
    (map_every qx_gen_tac [`fuel`,`gs`,`tail`,`events0`,`u`] >> strip_tac >>
     qspecl_then [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`(j,obs)`,`acts`,
       `blocks`,`calls`,`ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,
       `JointConfig stk PG G tn fn inst s oms om hs h`,`raw_slots`,`sites`,`unused`,
       `ms_tab`,`p`,`d`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`hin`,`h0`,
       `be`,`hbe`,`cnt`,`OK s`,`F`,`NONE`,`q`,`call_z`,`old_cuts`,`old_levels`,
       `M0`,`fuel`,`gs`,`tail`,`events0`,`u`] mp_tac dft_packet_cut_row_alignment >>
     (impl_tac >-
      (conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- simp[NoAsms] >>
       conj_tac >- (rpt gen_tac >> strip_tac >>
         `old = new` by (map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP ms_tab key = SOME old`,`FLOOKUP ms_tab key = SOME new`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         qpat_assum `old = new` SUBST1_TAC >> POP_ASSUM_LIST (K all_tac) >>
         irule LIST_REL_refl >> rw[] >> irule LIST_REL_refl >> simp[]) >>
       ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- (qpat_assum `Abbrev (call_z = _)`
         (ACCEPT_TAC o REWRITE_RULE[markerTheory.Abbrev_def]))) >>
       ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- (qpat_assum `!i ai ds ei qi zi. _ ==>
         ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei
            counti fronti closedi resti later. _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rewrite_tac[pairTheory.pair_CASE_def] >>
         BETA_TAC >> disch_then ACCEPT_TAC)) >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qpat_assum `FLOOKUP ms_tab (p,d) = SOME ms` (fn ms =>
       qpat_assum `LIST_REL (LIST_REL _) (TAKE q (THE (FLOOKUP ms_tab (p,d)))) kgss`
         (assume_tac o SRULE[ms])) >>
     qpat_assum `!F kgss tail u. _ /\ _ /\ _ ==> (!op. MEM op inst.inst_operands ==> _) /\ _`
       (drule_all_then ACCEPT_TAC)) >>
  `!f owner b block_init k t.
    block_init.vs_inst_idx + k <= LENGTH b.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP block_init.vs_inst_idx b.bb_instructions)) /\
    FOLDR (dft_exec_cons f C7) OK (TAKE k (DROP block_init.vs_inst_idx b.bb_instructions)) block_init = OK t ==>
    t.vs_inst_idx = block_init.vs_inst_idx + k /\
    exec_block f C7 b block_init = exec_block f C7 b t /\
    gas_events_block f C7 owner b block_init =
      gas_events_block f C7 owner
        (b with bb_instructions := TAKE (block_init.vs_inst_idx + k) b.bb_instructions) block_init ++
      gas_events_block f C7 owner b t` by
    (map_every qx_gen_tac [`f`,`owner`,`b`,`block_init`,`k`,`t`] >> strip_tac >>
     qspecl_then [`f`,`C7`,`owner`,`b`,`block_init`,`k`] mp_tac
       dftPacketOperationalPrefixTheory.dft_packet_block_prefix_operational >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     pure_rewrite_tac[LET_THM] >> BETA_TAC >>
     disch_then (qspec_then `t` (drule_then ACCEPT_TAC) o CONJUNCT1)) >>
  `!fuel gs tail. N <= fuel /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs ==>
     levels_ok fuel C7 old_levels (MAP (\(ai,ds,ei,qi,zi). ai) old_cuts)
       incoming0 root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
     (?extra. E0 = FST (rooted_eval fuel C7 old_levels
       (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
     (case SND (rooted_eval fuel C7 old_levels
        (root_entry with vs_gas_readings := gs ++ tail)) of
       OK u =>
         FST (rooted_eval fuel C7 old_levels
           (root_entry with vs_gas_readings := gs ++ tail)) = E0 /\
         u.vs_gas_readings = tail /\
         (!t'. rooted_eval fuel C7 old_levels
           (root_entry with vs_gas_readings := gs ++ t') =
           (E0,OK (u with vs_gas_readings := t'))) /\
         (?before after. trace_blocks [] 0 fuel C7 root_sf
           (root_entry with vs_gas_readings := gs ++ tail) =
           before ++ [((p,d,inst.inst_id),sf,inst,u)] ++ after /\
           trace_gas before = ZIP (K0,gs)) /\
         (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
         (!callee argv. setup_callee callee argv
           (u with vs_gas_readings := s.vs_gas_readings) = setup_callee callee argv s) /\
         (!bb0. lookup_block u.vs_current_bb sf.fn_blocks = SOME bb0 ==>
           ?K : exec_result -> (string # num) list # exec_result.
             run_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
               SND (K (exec_block (fuel-d) C7 bb0 u)) /\
             gas_events_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
               E0 ++ gas_events_block (fuel-d) C7 sf.fn_name bb0 u ++
                 FST (K (exec_block (fuel-d) C7 bb0 u)) /\
             (!v. K (Halt v) = ([],Halt v)) /\
             (!a v. K (Abort a v) = ([],Abort a v)) /\
             (!msg. K (Error msg) = ([],Error msg)))
       | stopped =>
         run_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
         gas_events_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
           FST (rooted_eval fuel C7 old_levels (root_entry with vs_gas_readings := gs ++ tail)))` by
    (map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
     qpat_assum `!F gs tail. _ ==> levels_ok F C7 old_levels _ _ _ _ _ _ /\ _`
       (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `Abbrev (incoming0 = _)`
       (fn inc => rewrite_tac[GSYM (SRULE [markerTheory.Abbrev_def] inc)]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (CONJUNCTS_THEN2 assume_tac (mk_asm "parent cut outcome"))) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qabbrev_tac `ent0 = root_entry with vs_gas_readings := gs ++ tail` >>
     asm_x "parent cut outcome" mp_tac >>
     Cases_on `rooted_eval fuel C7 old_levels ent0` >>
     rename1 `rooted_eval fuel C7 old_levels ent0 = (ev0,result0)` >>
     Cases_on `result0` >> simp[NoAsms] >>
     rename1 `rooted_eval fuel C7 old_levels ent0 = (ev0,OK u)` >>
     strip_tac >>
     `rooted_eval fuel C7 old_levels (root_entry with vs_gas_readings := gs ++ tail) =
       (ev0,OK u)` by (qpat_assum `Abbrev (ent0 = _)`
        (fn def => rewrite_tac[GSYM (SRULE [markerTheory.Abbrev_def] def)]) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!fuel gs tail ev u. _ ==> (!op. MEM op inst.inst_operands ==> _) /\ _`
       (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (qpat_assum `inst = EL (LENGTH call_z) _` (fn th => rewrite_tac[th]) >>
        rpt (goal_assum (drule_at Any)))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     `old_levels = pre ++ [(sf,
        (MAP (\f. case THE (FLOOKUP blocks (p,f)) of
          (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
            (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) caller_rows) ++
        [(bb,d,call_z)],NONE)]` by
       (qpat_assum `plan = MAP _ caller_rows ++ _` (fn th => rewrite_tac[GSYM th]) >>
        first_assum ACCEPT_TAC) >>
     qspecl_then [`fuel`,`C7`,`row_eval`,`plan_eval`,`call_setup`,`rooted_eval`,
       `plan_ok`,`levels_ok`,`old_levels`,`MAP (\(ai,ds,ei,qi,zi). ai) old_cuts`,
       `incoming0`,`root_sf`,`ent0`,
       `[]`,`0`,`pre`,`sf`,`MAP (\f. case THE (FLOOKUP blocks (p,f)) of
        (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
          (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) caller_rows`,
       `bb`,`d`,`call_z`,`ev0`,`u`] mp_tac
       dftPacketRootedOperationalTheory.dft_packet_rooted_success_operational >>
     (impl_tac >-
      (map_every (fn pat => conj_tac >-
        (qpat_assum pat mp_tac >> POP_ASSUM_LIST (K all_tac) >>
         rewrite_tac[pairTheory.pair_CASE_def] >> BETA_TAC >> disch_then ACCEPT_TAC))
        [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
         `plan_ok = _`,`levels_ok = _`] >>
       (conj_tac >-
        (qpat_assum `!f owner b st k t. _ ==> t.vs_inst_idx = _ /\ _ /\ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[])) >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     pure_rewrite_tac[arithmeticTheory.SUB_0] >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
         (qx_choose_then `continuation` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
     `bb0 = bb` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`lookup_block u.vs_current_bb sf.fn_blocks = SOME bb0`,
          `lookup_block u.vs_current_bb sf.fn_blocks = SOME bb`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qexists_tac `continuation` >>
     qpat_assum `Abbrev (ent0 = _)`
       (fn th => rewrite_tac[GSYM (SRULE[markerTheory.Abbrev_def] th)]) >>
     qpat_assum `bb0 = bb` SUBST1_TAC >>
     qpat_assum `ev0 = E0` (fn th => rewrite_tac[GSYM th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "call_fresh_cut_transport"
QED
Resume dft_focus_packet_step_retained[call_fresh_cut_transport]:
  qabbrev_tac `cuts1 = old_cuts ++ [(bpath,[],SUC d,vq,vz)]` >>
  qabbrev_tac `levels1 = pre ++ [(sf,plan,SOME inst);(csf,[(cbb,SUC d,vz)],NONE)]` >>
  qabbrev_tac `childM = FLAT (TAKE vq cm)` >>
  qabbrev_tac `childE = FLAT (TAKE vq ce)` >>
  qabbrev_tac `childK = FLAT (TAKE vq ck)` >>
  qabbrev_tac `newM = M0 ++ childM` >>
  qabbrev_tac `newE = E0 ++ childE` >>
  qabbrev_tac `newK = K0 ++ childK` >>
  `LAST old_cuts = (p,caller_rows,d,q,call_z)` by
    (qpat_assum `old_cuts = past ++ _` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  `MEM cbb csf.fn_blocks` by
    (qpat_assum `lookup_block cs.vs_current_bb csf.fn_blocks = SOME cbb` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  `EL (LENGTH call_z)
       (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst` by
    (sym_tac >> first_assum ACCEPT_TAC) >>
  `SUC d <= N'` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry)`,
        `EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) = _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     drule_all native_trace_blocks_continuation >> simp[] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `phi_prefix_length (cps ++ cys) = phi_prefix_length cbb.bb_instructions` by
    (qpat_assum `cbt.bb_instructions = cps ++ cys` (SUBST1_TAC o SYM) >>
     qpat_assum `phi_prefix_length cbb.bb_instructions = phi_prefix_length cps` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `(IS_SOME cbe /\ _) \/ (cbe = NONE /\ _)`
    (assume_tac o SRULE []) >>
  `inst = EL q xs` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH old_cuts = LENGTH (pre ++ [(sf,plan,NONE)])` by
    (qpat_assum `old_levels = pre ++ _` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `eval_phis cs (cps ++ cys) = OK sp` by
    (qpat_assum `cbt.bb_instructions = cps ++ cys` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (dftPacketCallFreshRootTheory.dft_packet_call_fresh_root_cut |> Q.INST
    [`c` |-> `inst`, `ctf` |-> `callee`, `b0` |-> `s`, `child_entry` |-> `cs`,
     `q0` |-> `q`, `ds` |-> `caller_rows`, `xs0` |-> `xs`, `bb0` |-> `bb`, `z0` |-> `call_z`,
     `cuts` |-> `old_cuts`, `incoming` |-> `incoming0`, `b` |-> `bpath`,
     `cb` |-> `cbb`, `cbt` |-> `cbt`, `csp` |-> `sp`, `be` |-> `s1`,
     `q` |-> `vq`, `z` |-> `vz`, `m` |-> `phi_prefix_length cbb.bb_instructions`,
     `k` |-> `LENGTH (vz:instruction list)`, `l` |-> `s1.vs_inst_idx`, `ci` |-> `inst'`,
     `g` |-> `N' - SUC d`, `Mc` |-> `childM`, `Ec` |-> `childE`, `Kc` |-> `childK`,
     `cuts'` |-> `cuts1`, `levels'` |-> `levels1`,
     `M'` |-> `newM`, `E'` |-> `newE`, `K'` |-> `newK`, `N'` |-> `MAX N (SUC d)`]) >>
  (impl_tac >-
    (rpt (conj_tac >- FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
     (conj_tac >-
      (qpat_x_assum `(IS_SOME cbe /\ vq < LENGTH cxs /\ _) \/ (cbe = NONE /\ _)`
         strip_assume_tac
       >- (disj1_tac >>
           `has_body` by (qpat_assum `IS_SOME cbe` (fn th => simp[NoAsms,Abbr `has_body`,th])) >>
           qpat_assum `has_body` (fn head => qpat_assum `cbe = if has_body then _ else _`
             (fn body => qpat_assum `case cbe of NONE => _ | SOME _ => _`
               (MAP_EVERY assume_tac o CONJUNCTS o SRULE[head,body]))) >>
           (conj_tac >-
             (qpat_assum `cbt.bb_instructions = cps ++ cys` (SUBST1_TAC o SYM) >>
              first_assum (ACCEPT_TAC o Q.SPECL [`N' - SUC d`,`C8`]))) >>
           rpt (conj_tac >- first_assum ACCEPT_TAC) >>
           (conj_tac >-
             (map_every (fn pat => qpat_assum pat mp_tac)
                 [`EVERY (\i. ~is_terminator i.inst_opcode) (TAKE vq cxs)`,
                  `!r. (EL r cxs).inst_opcode = INVOKE ==> ~(r < vq)`,
                  `vq < LENGTH cxs`] >>
              POP_ASSUM_LIST (K all_tac) >>
              simp[EVERY_EL,LENGTH_TAKE,EL_TAKE] >> metis_tac[])) >>
           (conj_tac >- first_assum ACCEPT_TAC) >>
           (conj_tac >-
             (map_every (fn pat => qpat_assum pat mp_tac)
                [`vq < LENGTH cxs`,`vz = _`] >>
              POP_ASSUM_LIST (K all_tac) >> simp[LENGTH_TAKE,LENGTH_DROP])) >>
           map_every (fn pat => conj_tac >-
             (qpat_assum `has_body` (fn head => qpat_assum pat
                (fn th => simp[NoAsms,SRULE[markerTheory.Abbrev_def,head] th]))))
             [`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
           map_every (fn pat => conj_tac >-
             qpat_assum pat (ACCEPT_TAC o REWRITE_RULE[markerTheory.Abbrev_def]))
             [`Abbrev (childM = _)`,`Abbrev (childE = _)`,`Abbrev (childK = _)`] >>
           (conj_tac >-
             (qpat_assum `cbb.bb_label = cs.vs_current_bb` SUBST1_TAC >>
              first_assum ACCEPT_TAC)) >>
           (conj_tac >-
             (qpat_assum `cbb.bb_label = cs.vs_current_bb` SUBST1_TAC >>
              first_assum ACCEPT_TAC)) >>
           rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
       disj2_tac >>
       qpat_assum `cbe = NONE` (fn is_none => qpat_assum `case cbe of NONE => _ | SOME _ => _`
         (MAP_EVERY assume_tac o CONJUNCTS o SRULE[is_none])) >>
       (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >-
         (qpat_assum `phi_prefix_length (cps ++ cys) = phi_prefix_length cbb.bb_instructions`
           (SUBST1_TAC o SYM) >>
          qpat_assum `cbt.bb_instructions = cps ++ cys` (SUBST1_TAC o SYM) >>
          first_assum ACCEPT_TAC)) >>
       (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >-
         (qpat_assum `cbt.bb_instructions = cps ++ cys` (SUBST1_TAC o SYM) >>
          first_assum (ACCEPT_TAC o Q.SPECL [`N' - SUC d`,`C8`]))) >>
       (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >-
         (map_every (fn pat => qpat_assum pat mp_tac)
           [`s1.vs_inst_idx < LENGTH cps`,`vz = _`] >>
          POP_ASSUM_LIST (K all_tac) >> simp[LENGTH_TAKE,LENGTH_DROP])) >>
       qpat_assum `vq = 0` (fn z => simp[NoAsms,z,Abbr `childM`,Abbr `childE`,Abbr `childK`]))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (qpat_assum `old_levels = pre ++ _` (fn th => rewrite_tac[GSYM th]) >>
        first_assum ACCEPT_TAC)) >>
     simp[NoAsms,Abbr `cuts1`,Abbr `levels1`,Abbr `newM`,Abbr `newE`,Abbr `newK`])) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `q < LENGTH ms /\ q < LENGTH ess /\ q < LENGTH ks` by
    (qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        FLOOKUP blocks (a,e) = _ /\ _ ==> LENGTH ms = LENGTH xs /\ _`
      (qspecl_then [`p`,`d`] (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`q < LENGTH xs`,`LENGTH ms = LENGTH xs`,`LENGTH ess = LENGTH ms`,`LENGTH ks = LENGTH ms`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `FDOM ms' = FDOM blocks' /\ FDOM es' = FDOM blocks' /\ FDOM ks' = FDOM blocks'` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks' = _`,`FDOM ms' = _`,`FDOM es' = _`,`FDOM ks' = _`,
        `FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,`FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!i ai ds ei qi zi.
    i < LENGTH old_cuts /\ EL i old_cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi
     bei hbei counti fronti closedi resti later mi esi ki.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,
        SOME (bei,hbei),counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\ ALL_DISTINCT orderi /\
      ALL_DISTINCT (MAP (\inst. inst.inst_id) xsi) /\
      FLOOKUP ms_tab (ai,ei) = SOME mi /\ FLOOKUP es_tab (ai,ei) = SOME esi /\
      FLOOKUP ks_tab (ai,ei) = SOME ki /\
      LENGTH mi = LENGTH xsi /\ LENGTH esi = LENGTH xsi /\ LENGTH ki = LENGTH xsi /\
      qi < LENGTH xsi /\
      (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi)) /\
      (SUC i < LENGTH old_cuts ==>
        ?cid hh b0 done child ret csf ctf cinc corder cres crest.
          FST (EL (SUC i) old_cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,hh,b0,done,child,ret) /\
          (EL qi xsi).inst_opcode = INVOKE /\ (EL qi xsi).inst_id = cid /\
          FLOOKUP acts ((ei,cid)::ai) = SOME (csf,ctf,cinc,child,corder,cres,crest) /\
          EL qi mi = AM ((ei,cid)::ai) /\ EL qi esi = AE ((ei,cid)::ai) /\
          EL qi ki = AK ((ei,cid)::ai))` by
    (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
     let val row = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,
                      `psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bodyi`,`counti`,`fronti`,
                      `closedi`,`resti`,`later`]
     in
       qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
                   bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
         (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then
            (List.foldr (fn (q,k) => qx_choose_then q k)
              (MAP_EVERY assume_tac o CONJUNCTS) row)))
     end >>
     `?bei hbei. bodyi = SOME (bei,hbei) /\ qi < LENGTH xsi /\
       (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi))` by
       (Cases_on `SUC i = LENGTH old_cuts`
        >- (qpat_assum `SUC i = LENGTH old_cuts` (fn guard =>
              qpat_assum `if SUC i = LENGTH old_cuts then _ else _`
                (strip_assume_tac o REWRITE_RULE [guard])) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`FLOOKUP blocks (ai,ei) = SOME _`,
               `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,OK s,F,NONE)`,
               `ai = p`,`ei = d`,`qi = q`,`q < LENGTH xs`,
               `!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE cnt sched)`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
            qexistsl [`be`,`hbe`] >> simp[]) >>
        qpat_assum `SUC i <> LENGTH old_cuts` (fn guard =>
          qpat_assum `if SUC i = LENGTH old_cuts then _ else _`
            (strip_assume_tac o REWRITE_RULE [guard])) >>
        qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
          (qspecl_then [`ai`,`ei`,`cid`] (drule_then
            (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)))) >>
        `!r. MEM r done_at_call ==> MEM r (TAKE counti rhoi)` by
          (qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
             mp_tac >>
           qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,bodyi,_,_,_,_)` mp_tac >>
           qpat_assum `FLOOKUP calls (ai,ei,cid) = SOME (_,_,_,done_at_call,_,_)` mp_tac >>
           qhdtm_assum `dft_focus_packet_rel` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
           drule_all dft_packet_call_done_contained >> gvs[]) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`,
           `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,bodyi,_,_,_,_)`,
           `qi < LENGTH _`,`!r. r < qi /\ _ ==> MEM r done_at_call`,
           `!r. MEM r done_at_call ==> _`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
     qpat_assum `bodyi = SOME (bei,hbei)` SUBST_ALL_TAC >>
     `?mi esi ki. FLOOKUP ms_tab (ai,ei) = SOME mi /\
         FLOOKUP es_tab (ai,ei) = SOME esi /\ FLOOKUP ks_tab (ai,ei) = SOME ki` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
           `FDOM blocks = FDOM ks_tab`,`FLOOKUP blocks (ai,ei) = SOME _`] >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
                   _ ==> LENGTH ms = LENGTH xs /\ _`
       (qspecl_then [`ai`,`ei`] (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME _ ==> _`
       (qspec_then `ai` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     `ALL_DISTINCT orderi` by
       (qpat_assum `orderi = GENLIST _ _` (SUBST1_TAC) >> simp[NoAsms,ALL_DISTINCT_GENLIST]) >>
     `ALL_DISTINCT (MAP (\inst. inst.inst_id) xsi)` by
       (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
                     FLOOKUP blocks (a,e) = _ ==> _`
          (qspecl_then [`ai`,`ei`] (drule_then mp_tac)) >>
        qpat_assum `FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)` SUBST1_TAC >>
        qpat_assum `dft_fn_rel sfi tfi` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        simp[] >> rpt strip_tac >>
        `wf_function sfi /\ MEM bbi sfi.fn_blocks` by
          metis_tac[dft_fn_rel_def,venomExecProofsTheory.lookup_block_MEM] >>
        `ALL_DISTINCT (MAP (\inst. inst.inst_id) bbi.bb_instructions)` by
          (irule dftWfTheory.wf_fn_block_inst_ids_distinct >> qexists `sfi` >> simp[]) >>
        pop_assum mp_tac >> simp[ALL_DISTINCT_APPEND]) >>
     qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,`psi`,
               `xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`hbei`,`counti`,`fronti`,`closedi`,
               `resti`,`later`,`mi`,`esi`,`ki`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH esi = LENGTH mi`,`LENGTH mi = LENGTH xsi`] >>
       POP_ASSUM_LIST (K all_tac) >> simp[])) >>
     (conj_tac >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ki = LENGTH mi`,`LENGTH mi = LENGTH xsi`] >>
       POP_ASSUM_LIST (K all_tac) >> simp[])) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     `SUC i <> LENGTH old_cuts` by
       (pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `SUC i <> LENGTH old_cuts` (fn guard =>
       qpat_assum `if SUC i = LENGTH old_cuts then _ else _`
         (strip_assume_tac o REWRITE_RULE [guard])) >>
     `FST (EL (SUC i) old_cuts) = (ei,cid)::ai` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`EL (SUC i) (MAP _ old_cuts) = (ei,cid)::ai`,`SUC i < LENGTH old_cuts`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[EL_MAP] >>
        Cases_on `EL (SUC i) old_cuts` >> rename1 `_ = (path,payload)` >>
        PairCases_on `payload` >> simp[]) >>
     qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
       (qspecl_then [`ai`,`ei`,`cid`] (drule_then mp_tac)) >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`FLOOKUP blocks (ai,ei) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,SOME (bei,hbei),counti,fronti,closedi,resti)`,
        `FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)`] >>
     simp[NoAsms] >> disch_then (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qpat_assum `!sf tf inc entry order res nrest.
         FLOOKUP acts ai = SOME _ ==> (!q. q < LENGTH xsi ==> _) /\ _`
       (fn rule => qpat_assum `FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)`
         (mp_then Any (qspec_then `qi` assume_tac o CONJUNCT1) rule)) >>
     qexistsl [`h'`,`b0`,`done_at_call`,`child_entry`,`ret`,`csf'`,`ctf`,
               `ei`,`child_order`,`child_res`,`child_rest`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FST (EL (SUC i) old_cuts) = (ei,cid)::ai`,`(EL qi xsi).inst_id = cid`,
        `(EL qi xsi).inst_opcode = INVOKE`,`qi < LENGTH xsi`,
        `FLOOKUP calls (ai,ei,cid) = SOME (qi,h',b0,done_at_call,child_entry,ret)`,
        `FLOOKUP acts ((ei,cid)::ai) = SOME (csf',ctf,ei,child_entry,child_order,child_res,child_rest)`,
        `qi < LENGTH xsi ==> _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  `!i ai ds ei qi zi.
    i < LENGTH old_cuts /\ EL i old_cuts = (ai,ds,ei,qi,zi) ==>
    (?sfi tfi inci enti orderi resi nresti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      orderi = ds ++ ei::later) /\
    (!f. MEM f ds ==> FLOOKUP blocks' (ai,f) = FLOOKUP blocks (ai,f)) /\
    (SUC i < LENGTH old_cuts ==> !cid.
      FST (EL (SUC i) old_cuts) = (ei,cid)::ai ==>
      FLOOKUP calls' (ai,ei,cid) = FLOOKUP calls (ai,ei,cid)) /\
    qi < LENGTH (THE (FLOOKUP ms' (ai,ei))) /\
    qi < LENGTH (THE (FLOOKUP es' (ai,ei))) /\
    qi < LENGTH (THE (FLOOKUP ks' (ai,ei))) /\
    (SUC i < LENGTH old_cuts ==>
      EL qi (THE (FLOOKUP ms' (ai,ei))) = AM1 (FST (EL (SUC i) old_cuts)) /\
      EL qi (THE (FLOOKUP es' (ai,ei))) = AE1 (FST (EL (SUC i) old_cuts)) /\
      EL qi (THE (FLOOKUP ks' (ai,ei))) = AK1 (FST (EL (SUC i) old_cuts))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))` by
    (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
     let val witnesses = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,
                           `psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`hbei`,`counti`,
                           `fronti`,`closedi`,`resti`,`later`,`mi`,`esi`,`ki`]
     in
       qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
         bbi bti psi xsi ysi rhoi ini hi bei hbei counti fronti closedi resti later mi esi ki.
         _`
         (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then
           (List.foldr (fn (q,k) => qx_choose_then q k)
             (MAP_EVERY assume_tac o CONJUNCTS) witnesses)))
     end >>
     let
       fun pieces (tab,out,row,indexed_row,up,frame) =
         qspecl_then [`acts`,`blocks`,`calls`,tab,`acts'`,`blocks'`,`calls'`,out,
                      `(csf,callee,d,cs,[SUC d],NONE,NONE)`,
                      `(cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`,
                      `(q,j,s,TAKE cnt sched,cs,NONE)`,`p`,`d`,`inst.inst_id`,
                      `bpath`,`plen`,`inds`,`ords`,`ai`,`ds`,`ei`,`qi`,`zi`,
                      `sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`,
                      `bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`SOME (bei,hbei)`,
                      `counti`,`fronti`,`closedi`,`resti`,row]
           mp_tac dftPacketCallPathGeometryTheory.dft_packet_call_historical_pieces >>
         (impl_tac >-
           (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
            (conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
            (conj_tac >- first_assum ACCEPT_TAC) >>
            (conj_tac >- simp[NoAsms]) >>
            (conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
            conj_tac
            >- (qx_gen_tac `r` >> disch_tac >>
                let val all = [`osf`,`otf`,`oi`,`oen`,`ores`,`orest`,`eb`,`tb`,`eps`,
                   `exs`,`eys`,`erho`,`ein`,`eh`,`ebe`,`ehbe`,`ecnt`,`eb0`,
                   `rm`,`re`,`rk`]
                in
                  qpat_assum `!i. i < plen ==>
                    ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0 rm re rk. _`
                    (qspec_then `r` (drule_then (List.foldr (fn (q,k) => qx_choose_then q k)
                      (MAP_EVERY assume_tac o CONJUNCTS) all))) >>
                  qexistsl (List.take (all,17) @
                    [`OK eb0`,`F`,`NONE`,indexed_row])
                end >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
                first_assum ACCEPT_TAC) >>
            conj_tac
            >- (rpt strip_tac >> qpat_assum up (drule_all_then (ACCEPT_TAC o CONJUNCT1))) >>
            rpt strip_tac >> qpat_assum frame (drule_all_then (fn th =>
              FIRST (map ACCEPT_TAC (CONJUNCTS th)))))) >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS)
     in
       pieces (`ms_tab`,`ms'`,`mi`,`rm`,
         `!i rows. _ ==> FLOOKUP ms' _ = SOME (LUPDATE _ _ rows) /\ _`,
         `!a e. _ ==> FLOOKUP ms' (a,e) = _ /\ _`) >>
       pieces (`es_tab`,`es'`,`esi`,`re`,
         `!i rows. _ ==> FLOOKUP es' _ = SOME (LUPDATE _ _ rows) /\ _`,
         `!a e. _ ==> _ /\ FLOOKUP es' (a,e) = _ /\ _`) >>
       pieces (`ks_tab`,`ks'`,`ki`,`rk`,
         `!i rows. _ ==> FLOOKUP ks' _ = SOME (LUPDATE _ _ rows) /\ _`,
         `!a e. _ ==> _ /\ _ /\ FLOOKUP ks' (a,e) = _`)
     end >>
     let val child = [`ccid`,`chh`,`cb0`,`cdone`,`cchild`,`cret`,`csfi`,`ctfi`,
                      `cinci`,`cordi`,`cresi`,`cresti`]
         val get_child = qpat_assum `SUC i < LENGTH old_cuts ==> ?cid hh b0 done child ret
             csf ctf cinc corder cres crest. FST (EL (SUC i) old_cuts) = _ /\ _`
           (drule_then (List.foldr (fn (q,k) => qx_choose_then q k)
             (MAP_EVERY assume_tac o CONJUNCTS) child))
     in
       (conj_tac >- (qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`] >>
                     conj_tac >> first_assum ACCEPT_TAC)) >>
       (conj_tac >- (qx_gen_tac `f` >> disch_tac >>
         qpat_assum `!f. MEM f ds ==> FLOOKUP blocks' (ai,f) = FLOOKUP blocks (ai,f) /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
       (conj_tac >- (disch_tac >> get_child >> qx_gen_tac `cid` >>
         qpat_assum `!key v. FLOOKUP calls key = SOME v ==> _`
           (qspec_then `(ai,ei,ccid)` (drule_then assume_tac)) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`FST (EL (SUC i) old_cuts) = (ei,ccid)::ai`,
            `FLOOKUP calls (ai,ei,ccid) = SOME (qi,chh,cb0,cdone,cchild,cret)`,
            `FLOOKUP calls' (ai,ei,ccid) = SOME (qi,chh,cb0,cdone,cchild,cret)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])) >>
       map_every (fn (len,oldlen) => conj_tac >-
         (map_every (fn pat => qpat_assum pat mp_tac) [len,oldlen,`qi < LENGTH xsi`] >>
          POP_ASSUM_LIST (K all_tac) >> simp[]))
         [(`LENGTH (THE (FLOOKUP ms' (ai,ei))) = LENGTH mi`,`LENGTH mi = LENGTH xsi`),
          (`LENGTH (THE (FLOOKUP es' (ai,ei))) = LENGTH esi`,`LENGTH esi = LENGTH xsi`),
          (`LENGTH (THE (FLOOKUP ks' (ai,ei))) = LENGTH ki`,`LENGTH ki = LENGTH xsi`)] >>
       (conj_tac >- (disch_tac >> get_child >>
         qpat_assum `FST (EL (SUC i) old_cuts) = (ei,ccid)::ai` SUBST1_TAC >>
         let
           val old_child = `FLOOKUP acts ((ei,ccid)::ai) = SOME (_,_,_,_,cordi,_,_)`
           fun final_cell (cell,old_agg,new_agg,result) =
             qpat_assum old_agg (fn agg => qpat_assum old_child (fn lk =>
               qpat_assum cell (assume_tac o SRULE [agg,lk]))) >>
             qpat_assum result (qspec_then `ccid` (drule_all_then
               (MAP_EVERY assume_tac o CONJUNCTS))) >>
             qpat_assum new_agg (fn agg =>
               qpat_assum `FLOOKUP acts' ((ei,ccid)::ai) = SOME (_,_,_,_,cordi,_,_)`
                 (fn lk => simp[NoAsms,SRULE [markerTheory.Abbrev_def] agg,lk])) >>
             first_assum ACCEPT_TAC
         in
           conj_tac
           >- final_cell (`EL qi mi = AM _`,`AM = _`,`Abbrev (AM1 = _)`,
               `!cid h b0 done child ret sf tf inc entry ord res rest. _ ==> _ /\ _ /\ EL qi (THE (FLOOKUP ms' (ai,ei))) = _`) >>
           conj_tac
           >- final_cell (`EL qi esi = AE _`,`AE = _`,`Abbrev (AE1 = _)`,
               `!cid h b0 done child ret sf tf inc entry ord res rest. _ ==> _ /\ _ /\ EL qi (THE (FLOOKUP es' (ai,ei))) = _`) >>
           final_cell (`EL qi ki = AK _`,`AK = _`,`Abbrev (AK1 = _)`,
             `!cid h b0 done child ret sf tf inc entry ord res rest. _ ==> _ /\ _ /\ EL qi (THE (FLOOKUP ks' (ai,ei))) = _`)
         end)) >>
       map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
         [`FLOOKUP ms_tab (ai,ei) = SOME mi`, `FLOOKUP es_tab (ai,ei) = SOME esi`,
          `FLOOKUP ks_tab (ai,ei) = SOME ki`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC
     end) >>
  `(!i ai ds ei qi zi.
    i < LENGTH cuts1 /\ EL i cuts1 = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks' (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts1 then
        ai = bpath /\ ei = SUC d /\ qi = vq /\ zi = vz
      else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts1) = (ei,cid)::ai /\
          FLOOKUP calls' (ai,ei,cid) =
            SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
            MEM r done_at_call)) /\
      EL i levels1 =
        (sfi,
         MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++
           [(bbi,ei,zi)],
         if SUC i = LENGTH cuts1 then NONE else SOME (EL qi xsi)))` by
    (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >>
     strip_tac >>
     `LENGTH cuts1 = SUC (LENGTH old_cuts)` by simp[NoAsms,Abbr `cuts1`] >>
     reverse (Cases_on `i < LENGTH old_cuts`)
     >- (`i = LENGTH old_cuts` by
          (map_every (fn pat => qpat_assum pat mp_tac)
           [`i < LENGTH cuts1`,`~(i < LENGTH old_cuts)`,
            `LENGTH cuts1 = SUC (LENGTH old_cuts)`] >>
           POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
         `EL i cuts1 = (bpath,[],SUC d,vq,vz)` by
           (qpat_assum `i = LENGTH old_cuts` SUBST1_TAC >>
            simp[NoAsms,Abbr `cuts1`,EL_APPEND_EQN]) >>
         qpat_assum `EL i cuts1 = (bpath,[],SUC d,vq,vz)` (fn th =>
           qpat_x_assum `EL i cuts1 = (ai,ds,ei,qi,zi)`
             (MAP_EVERY (SUBST_ALL_TAC o SYM) o CONJUNCTS o
               PURE_REWRITE_RULE [th,pairTheory.PAIR_EQ])) >>
         `SUC i = LENGTH cuts1` by
           (qpat_assum `i = LENGTH old_cuts` SUBST1_TAC >> sym_tac >> first_assum ACCEPT_TAC) >>
         `i = SUC (LENGTH pre)` by
           (map_every (fn pat => qpat_assum pat mp_tac)
             [`i = LENGTH old_cuts`,`LENGTH old_cuts = LENGTH old_levels`,
              `old_levels = pre ++ _`] >> POP_ASSUM_LIST (K all_tac) >> simp[]) >>
         qexistsl [`csf`,`callee`,`d`,`cs`,`[SUC d]`,`NONE`,`NONE`,
           `cbb`,`cbt`,`cps`,`cxs`,`cys`,`crho`,`cs`,`SUC j`,`cbe`,
           `0`,`OK s1`,`F`,`NONE`,`[]`] >>
         qpat_assum `SUC i = LENGTH cuts1` (fn th => simp[NoAsms,th]) >>
         qpat_assum `i = SUC (LENGTH pre)` (fn th => simp[NoAsms,th,Abbr `levels1`,EL_APPEND_EQN]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `EL i old_cuts = (ai,ds,ei,qi,zi)` by
       (qpat_assum `EL i cuts1 = _` mp_tac >> qpat_assum `i < LENGTH old_cuts` mp_tac >>
        qpat_assum `Abbrev (cuts1 = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL_APPEND1]) >>
     `SUC i <> LENGTH cuts1` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`i < LENGTH old_cuts`,`LENGTH cuts1 = SUC (LENGTH old_cuts)`] >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     let val witnesses = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,
           `bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bodyi`,
           `counti`,`fronti`,`closedi`,`resti`,`later`]
     in
       qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
           bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
              FLOOKUP acts ai = _ /\ FLOOKUP blocks (ai,ei) = _ /\ _`
         (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then
           (List.foldr (fn (q,k) => qx_choose_then q k)
             (MAP_EVERY assume_tac o CONJUNCTS) witnesses))) >>
       qexistsl witnesses
     end >>
     `ai <> bpath` by
       (map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP acts ai = SOME _`,`FLOOKUP acts bpath = NONE`] >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
     `!e. FLOOKUP blocks' (ai,e) = FLOOKUP blocks (ai,e)` by
       (qx_gen_tac `dep` >> qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
         (qspecl_then [`ai`,`dep`] mp_tac) >> qpat_assum `ai <> bpath` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     (conj_tac >- (qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = _`
        (qspec_then `ai` (drule_then (fn th => rewrite_tac[th]))) >>
        first_assum ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `!e. FLOOKUP blocks' (ai,e) = FLOOKUP blocks (ai,e)`
        (qspec_then `ei` (fn th => rewrite_tac[th])) >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     `MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds =
       MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds` by
       (qpat_assum `!e. FLOOKUP blocks' (ai,e) = FLOOKUP blocks (ai,e)`
         (fn th => simp[NoAsms,th])) >>
     Cases_on `SUC i = LENGTH old_cuts`
     >- (qpat_assum `SUC i = LENGTH old_cuts` (fn th =>
          qpat_x_assum `if SUC i = LENGTH old_cuts then _ else _`
            (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS o REWRITE_RULE[th])) >>
         `EL q xsi = inst /\ bbi = bb /\ psi = ps /\ xsi = xs /\ sfi = sf /\ ds = caller_rows` by
           (map_every (fn pat => qpat_assum pat mp_tac)
            [`FLOOKUP acts p = SOME (sfi,_,_,_,_,_,_)`,
             `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
             `FLOOKUP blocks (p,d) = SOME (bbi,_,_,_,_,_,_,_,_,_,_,_,_)`,
             `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,OK s,F,NONE)`,
             `EL q xs = inst`,`EL i old_cuts = _`,`old_cuts = past ++ _`,
             `SUC i = LENGTH old_cuts`] >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[EL_APPEND_EQN] >> rpt strip_tac >>
            `i = LENGTH past` by
              (map_every (fn pat => qpat_assum pat mp_tac)
                 [`SUC i = LENGTH old_cuts`,`old_cuts = past ++ _`] >>
               POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
            gvs[EL_APPEND_EQN]) >>
         map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
           [`bbi = bb`,`psi = ps`,`xsi = xs`,`sfi = sf`,`ds = caller_rows`] >>
         qpat_assum `SUC i <> LENGTH cuts1` (fn guard =>
           qpat_assum `EL q xs = inst` (fn curr => simp[NoAsms,guard,curr,Abbr `call_z`])) >>
         (conj_tac >-
          (qexistsl [`j`,`s`,`TAKE cnt sched`,`cs`,`NONE`] >>
           (conj_tac >-
            (map_every (fn pat => qpat_assum pat mp_tac)
               [`SUC i = LENGTH old_cuts`, `bpath = (d,inst.inst_id)::p`,`Abbrev (cuts1 = _)`] >>
             POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL_APPEND_EQN,MAP_APPEND])) >>
           rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         `i = LENGTH pre` by
           (map_every (fn pat => qpat_assum pat mp_tac)
             [`SUC i = LENGTH old_cuts`,`LENGTH old_cuts = LENGTH old_levels`,
              `old_levels = pre ++ _`] >>
            POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`i = LENGTH pre`,`plan = MAP _ caller_rows ++ _`,
            `EL q xs = inst`,`MAP _ caller_rows = MAP _ caller_rows`,
            `Abbrev (levels1 = _)`] >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[markerTheory.Abbrev_def,pairTheory.pair_CASE_def,EL_APPEND_EQN]) >>
     `SUC i < LENGTH old_cuts` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`i < LENGTH old_cuts`,`SUC i <> LENGTH old_cuts`] >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `SUC i <> LENGTH old_cuts` (fn guard =>
       qpat_assum `if SUC i = LENGTH old_cuts then _ else _`
         (strip_assume_tac o REWRITE_RULE[guard])) >>
     qpat_assum `SUC i <> LENGTH cuts1` (fn guard => rewrite_tac[guard]) >>
     (conj_tac >-
      (qexistsl [`cid`,`h'`,`b0`,`done_at_call`,`child_entry`,`ret`] >>
       (conj_tac >-
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`SUC i < LENGTH old_cuts`,`EL (SUC i) (MAP _ old_cuts) = _`,`Abbrev (cuts1 = _)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL_APPEND1,MAP_APPEND])) >>
       (conj_tac >- (qpat_assum `!key v. FLOOKUP calls key = SOME v ==> _`
          (qspec_then `(ai,ei,cid)` (drule_then ACCEPT_TAC)))) >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     `i < LENGTH pre` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`SUC i < LENGTH old_cuts`,`LENGTH old_cuts = LENGTH old_levels`,
          `old_levels = pre ++ _`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`EL i old_levels = _`,`i < LENGTH pre`,`old_levels = pre ++ _`,
        `SUC i <> LENGTH old_cuts`,`Abbrev (levels1 = _)`,`MAP _ ds = MAP _ ds`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,pairTheory.pair_CASE_def,EL_APPEND1]) >>
  suspend "call_cut_table_prefixes"
QED
Resume dft_focus_packet_step_retained[call_cut_table_prefixes]:
  `newM = FLAT (MAP (\(ai,ds,ei,qi,zi). FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms' (ai,ei))))) cuts1)` by
    (map_every (fn pat => qpat_assum pat
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (newM = _)`, `Abbrev (childM = _)`, `Abbrev (cuts1 = _)`] >>
     qpat_assum `M0 = FLAT _` SUBST1_TAC >>
     irule dftPacketSelectedCutTransportTheory.dft_packet_extend_selected_cut_rows >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _)
         /\ _` (fn th => rpt strip_tac >>
           drule_all_then (FIRST o map ACCEPT_TAC o CONJUNCTS) th)) >>
  `newE = FLAT (MAP (\(ai,ds,ei,qi,zi). FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es' (ai,ei))))) cuts1)` by
    (map_every (fn pat => qpat_assum pat
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (newE = _)`, `Abbrev (childE = _)`, `Abbrev (cuts1 = _)`] >>
     qpat_assum `E0 = FLAT _` SUBST1_TAC >>
     irule dftPacketSelectedCutTransportTheory.dft_packet_extend_selected_cut_rows >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _)
         /\ _` (fn th => rpt strip_tac >>
           drule_all_then (FIRST o map ACCEPT_TAC o CONJUNCTS) th)) >>
  `newK = FLAT (MAP (\(ai,ds,ei,qi,zi). FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks' (ai,ei))))) cuts1)` by
    (map_every (fn pat => qpat_assum pat
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (newK = _)`, `Abbrev (childK = _)`, `Abbrev (cuts1 = _)`] >>
     qpat_assum `K0 = FLAT _` SUBST1_TAC >>
     irule dftPacketSelectedCutTransportTheory.dft_packet_extend_selected_cut_rows >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _)
         /\ _` (fn th => rpt strip_tac >>
           drule_all_then (FIRST o map ACCEPT_TAC o CONJUNCTS) th)) >>
  `cuts1 <> [] /\ FST (HD cuts1) = []` by
    (qpat_assum `MAP _ cuts1 = REVERSE _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts1`
     >- (strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     PairCases_on `h` >> strip_tac >> pop_assum (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_REVERSE,GENLIST_EQ_NIL,GENLIST_LAST,DROP_LENGTH_TOO_LONG]) >>
  `LENGTH cuts1 = SUC (LENGTH old_cuts)` by simp[NoAsms,Abbr `cuts1`] >>
  `EL (LENGTH old_cuts) cuts1 = (bpath,[],SUC d,vq,vz)` by simp[NoAsms,Abbr `cuts1`,EL_APPEND2] >>
  `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts` by
     simp[NoAsms,Abbr `cuts1`,EL_APPEND1] >>
  `!i. i < LENGTH cuts1 ==> i < LENGTH old_cuts \/ i = LENGTH old_cuts` by
     (qpat_assum `LENGTH cuts1 = SUC (LENGTH old_cuts)` (fn th => rewrite_tac[th]) >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `vq <= LENGTH cm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`(IS_SOME cbe /\ vq < LENGTH cxs /\ _) \/ (cbe = NONE /\ _)`,
       `Abbrev (has_body = _)`,`Abbrev (cm = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >>
     rpt strip_tac >> simp[]) >>
  `EL q (THE (FLOOKUP ms' (p,d))) = AM1 bpath` by
    (`0 < plen` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`plen = LENGTH bpath`,`bpath = (d,inst.inst_id)::p`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qpat_assum `!i rows. i < plen /\ FLOOKUP ms_tab _ = SOME rows ==> _`
       (qspecl_then [`0`,`ms`] mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP ms_tab (p,d) = SOME ms`,`bpath = (d,inst.inst_id)::p`,
        `Abbrev (inds = _)`,`Abbrev (ords = _)`,`q < LENGTH ms`,`0 < plen`,
        `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`,
        `Abbrev (AM1 = _)`] >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[markerTheory.Abbrev_def] >> rpt strip_tac >>
     gvs[EL_LUPDATE,EL,GENLIST_CONS]) >>
  `?ms_rest. AM1 [] = newM ++ ms_rest` by
    (qpat_assum `newM = FLAT _` SUBST1_TAC >>
     Q.ISPECL_THEN [`acts'`,`ms'`,`ms'`,`cuts1`,`AM1`] mp_tac
       dftPacketSelectedCutTransportTheory.dft_packet_selected_cut_prefix >>
     (impl_tac >-
      (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- first_assum (ACCEPT_TAC o SRULE[markerTheory.Abbrev_def])) >>
       map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
       qpat_assum `!i. i < LENGTH cuts1 ==> _` (qspec_then `i` (drule_then strip_assume_tac)) >-
        (`EL i old_cuts = (ai,ds,ei,qi,zi)` by
           (qpat_assum `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts`
              (qspec_then `i` (drule_then (SUBST1_TAC o SYM))) >> first_assum ACCEPT_TAC) >>
         let val ws = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`]
         in
           qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _) /\ _`
             (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`]
               (drule_all_then (CONJUNCTS_THEN2
                 (List.foldr (fn (q,k) => qx_choose_then q k) strip_assume_tac ws)
                 (MAP_EVERY assume_tac o CONJUNCTS)))) >>
           qexistsl ws
         end >>
         qexists_tac `THE (FLOOKUP ms' (ai,ei))` >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >-
          (`(ai,ei) IN FDOM blocks'` by
             (qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
                bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
                   FLOOKUP acts' ai = _ /\ FLOOKUP blocks' (ai,ei) = _ /\ _`
               (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
              qpat_assum `FLOOKUP blocks' (ai,ei) = _` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF]) >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`(ai,ei) IN FDOM blocks'`, `FDOM ms' = FDOM blocks'`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF])) >>
         (conj_tac >- (qpat_assum `qi < LENGTH (THE (FLOOKUP ms' (ai,ei)))` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
         simp[NoAsms] >>
         disch_tac >> (conj_tac >- first_assum ACCEPT_TAC) >>
         Cases_on `SUC i < LENGTH old_cuts`
         >- (qpat_assum `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts`
               (qspec_then `SUC i` (drule_then SUBST1_TAC)) >>
             qpat_assum `SUC i < LENGTH old_cuts ==> EL qi (THE (FLOOKUP ms' (ai,ei))) = _ /\ _`
               (drule_then (FIRST o map ACCEPT_TAC o CONJUNCTS))) >>
         `SUC i = LENGTH old_cuts` by
           (map_every (fn pat => qpat_assum pat mp_tac)
             [`i < LENGTH old_cuts`,`~(SUC i < LENGTH old_cuts)`] >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
         `(ai,ei,qi) = (p,d,q)` by
           (`i = LENGTH past` by
              (map_every (fn pat => qpat_assum pat mp_tac)
                [`SUC i = LENGTH old_cuts`,`old_cuts = past ++ _`] >>
               POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`EL i old_cuts = _`,`old_cuts = past ++ _`,`i = LENGTH past`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`(ai,ei,qi) = (p,d,q)`,`SUC i = LENGTH old_cuts`,
            `EL (LENGTH old_cuts) cuts1 = _`,
            `EL q (THE (FLOOKUP ms' (p,d))) = AM1 bpath`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ]) >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`i = LENGTH old_cuts`,`EL i cuts1 = _`,`EL (LENGTH old_cuts) cuts1 = _`,
          `LENGTH cuts1 = SUC (LENGTH old_cuts)`] >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`FLOOKUP ms' (bpath,SUC d) = SOME cm`, `vq <= LENGTH cm`,
          `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`] >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[pairTheory.PAIR_EQ] >> rpt strip_tac >>
       qexistsl [`csf`,`callee`,`d`,`cs`,`NONE`,`NONE`,`[]`,`cm`] >>
       gvs[])) >>
     disch_then ACCEPT_TAC) >>
  `vq <= LENGTH ce` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`(IS_SOME cbe /\ vq < LENGTH cxs /\ _) \/ (cbe = NONE /\ _)`,
       `Abbrev (has_body = _)`,`Abbrev (ce = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >>
     rpt strip_tac >> simp[]) >>
  `EL q (THE (FLOOKUP es' (p,d))) = AE1 bpath` by
    (`0 < plen` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`plen = LENGTH bpath`,`bpath = (d,inst.inst_id)::p`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qpat_assum `!i rows. i < plen /\ FLOOKUP es_tab _ = SOME rows ==> _`
       (qspecl_then [`0`,`ess`] mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP es_tab (p,d) = SOME ess`,`bpath = (d,inst.inst_id)::p`,
        `Abbrev (inds = _)`,`Abbrev (ords = _)`,`q < LENGTH ess`,`0 < plen`,
        `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`,
        `Abbrev (AE1 = _)`] >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[markerTheory.Abbrev_def] >> rpt strip_tac >>
     gvs[EL_LUPDATE,EL,GENLIST_CONS]) >>
  `?es_rest. AE1 [] = newE ++ es_rest` by
    (qpat_assum `newE = FLAT _` SUBST1_TAC >>
     Q.ISPECL_THEN [`acts'`,`es'`,`es'`,`cuts1`,`AE1`] mp_tac
       dftPacketSelectedCutTransportTheory.dft_packet_selected_cut_prefix >>
     (impl_tac >-
      (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- first_assum (ACCEPT_TAC o SRULE[markerTheory.Abbrev_def])) >>
       map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
       qpat_assum `!i. i < LENGTH cuts1 ==> _` (qspec_then `i` (drule_then strip_assume_tac)) >-
        (`EL i old_cuts = (ai,ds,ei,qi,zi)` by
           (qpat_assum `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts`
              (qspec_then `i` (drule_then (SUBST1_TAC o SYM))) >> first_assum ACCEPT_TAC) >>
         let val ws = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`]
         in
           qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _) /\ _`
             (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`]
               (drule_all_then (CONJUNCTS_THEN2
                 (List.foldr (fn (q,k) => qx_choose_then q k) strip_assume_tac ws)
                 (MAP_EVERY assume_tac o CONJUNCTS)))) >>
           qexistsl ws
         end >>
         qexists_tac `THE (FLOOKUP es' (ai,ei))` >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >-
          (`(ai,ei) IN FDOM blocks'` by
             (qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
                bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
                   FLOOKUP acts' ai = _ /\ FLOOKUP blocks' (ai,ei) = _ /\ _`
               (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
              qpat_assum `FLOOKUP blocks' (ai,ei) = _` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF]) >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`(ai,ei) IN FDOM blocks'`, `FDOM es' = FDOM blocks'`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF])) >>
         (conj_tac >- (qpat_assum `qi < LENGTH (THE (FLOOKUP es' (ai,ei)))` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
         simp[NoAsms] >>
         disch_tac >> (conj_tac >- first_assum ACCEPT_TAC) >>
         Cases_on `SUC i < LENGTH old_cuts`
         >- (qpat_assum `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts`
               (qspec_then `SUC i` (drule_then SUBST1_TAC)) >>
             qpat_assum `SUC i < LENGTH old_cuts ==> EL qi (THE (FLOOKUP ms' (ai,ei))) = _ /\ _`
               (drule_then (FIRST o map ACCEPT_TAC o CONJUNCTS))) >>
         `SUC i = LENGTH old_cuts` by
           (map_every (fn pat => qpat_assum pat mp_tac)
             [`i < LENGTH old_cuts`,`~(SUC i < LENGTH old_cuts)`] >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
         `(ai,ei,qi) = (p,d,q)` by
           (`i = LENGTH past` by
              (map_every (fn pat => qpat_assum pat mp_tac)
                [`SUC i = LENGTH old_cuts`,`old_cuts = past ++ _`] >>
               POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`EL i old_cuts = _`,`old_cuts = past ++ _`,`i = LENGTH past`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`(ai,ei,qi) = (p,d,q)`,`SUC i = LENGTH old_cuts`,
            `EL (LENGTH old_cuts) cuts1 = _`,
            `EL q (THE (FLOOKUP es' (p,d))) = AE1 bpath`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ]) >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`i = LENGTH old_cuts`,`EL i cuts1 = _`,`EL (LENGTH old_cuts) cuts1 = _`,
          `LENGTH cuts1 = SUC (LENGTH old_cuts)`] >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`FLOOKUP es' (bpath,SUC d) = SOME ce`, `vq <= LENGTH ce`,
          `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`] >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[pairTheory.PAIR_EQ] >> rpt strip_tac >>
       qexistsl [`csf`,`callee`,`d`,`cs`,`NONE`,`NONE`,`[]`,`ce`] >>
       gvs[])) >>
     disch_then ACCEPT_TAC) >>
  `vq <= LENGTH ck` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`(IS_SOME cbe /\ vq < LENGTH cxs /\ _) \/ (cbe = NONE /\ _)`,
       `Abbrev (has_body = _)`,`Abbrev (ck = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >>
     rpt strip_tac >> simp[]) >>
  `EL q (THE (FLOOKUP ks' (p,d))) = AK1 bpath` by
    (`0 < plen` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`plen = LENGTH bpath`,`bpath = (d,inst.inst_id)::p`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[]) >>
     qpat_assum `!i rows. i < plen /\ FLOOKUP ks_tab _ = SOME rows ==> _`
       (qspecl_then [`0`,`ks`] mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP ks_tab (p,d) = SOME ks`,`bpath = (d,inst.inst_id)::p`,
        `Abbrev (inds = _)`,`Abbrev (ords = _)`,`q < LENGTH ks`,`0 < plen`,
        `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`,
        `Abbrev (AK1 = _)`] >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[markerTheory.Abbrev_def] >> rpt strip_tac >>
     gvs[EL_LUPDATE,EL,GENLIST_CONS]) >>
  `?ks_rest. AK1 [] = newK ++ ks_rest` by
    (qpat_assum `newK = FLAT _` SUBST1_TAC >>
     Q.ISPECL_THEN [`acts'`,`ks'`,`ks'`,`cuts1`,`AK1`] mp_tac
       dftPacketSelectedCutTransportTheory.dft_packet_selected_cut_prefix >>
     (impl_tac >-
      (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- first_assum (ACCEPT_TAC o SRULE[markerTheory.Abbrev_def])) >>
       map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
       qpat_assum `!i. i < LENGTH cuts1 ==> _` (qspec_then `i` (drule_then strip_assume_tac)) >-
        (`EL i old_cuts = (ai,ds,ei,qi,zi)` by
           (qpat_assum `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts`
              (qspec_then `i` (drule_then (SUBST1_TAC o SYM))) >> first_assum ACCEPT_TAC) >>
         let val ws = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`]
         in
           qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _) /\ _`
             (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`]
               (drule_all_then (CONJUNCTS_THEN2
                 (List.foldr (fn (q,k) => qx_choose_then q k) strip_assume_tac ws)
                 (MAP_EVERY assume_tac o CONJUNCTS)))) >>
           qexistsl ws
         end >>
         qexists_tac `THE (FLOOKUP ks' (ai,ei))` >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >-
          (`(ai,ei) IN FDOM blocks'` by
             (qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
                bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
                   FLOOKUP acts' ai = _ /\ FLOOKUP blocks' (ai,ei) = _ /\ _`
               (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
              qpat_assum `FLOOKUP blocks' (ai,ei) = _` mp_tac >>
              POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF]) >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`(ai,ei) IN FDOM blocks'`, `FDOM ks' = FDOM blocks'`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF])) >>
         (conj_tac >- (qpat_assum `qi < LENGTH (THE (FLOOKUP ks' (ai,ei)))` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
         simp[NoAsms] >>
         disch_tac >> (conj_tac >- first_assum ACCEPT_TAC) >>
         Cases_on `SUC i < LENGTH old_cuts`
         >- (qpat_assum `!i. i < LENGTH old_cuts ==> EL i cuts1 = EL i old_cuts`
               (qspec_then `SUC i` (drule_then SUBST1_TAC)) >>
             qpat_assum `SUC i < LENGTH old_cuts ==> EL qi (THE (FLOOKUP ms' (ai,ei))) = _ /\ _`
               (drule_then (FIRST o map ACCEPT_TAC o CONJUNCTS))) >>
         `SUC i = LENGTH old_cuts` by
           (map_every (fn pat => qpat_assum pat mp_tac)
             [`i < LENGTH old_cuts`,`~(SUC i < LENGTH old_cuts)`] >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
         `(ai,ei,qi) = (p,d,q)` by
           (`i = LENGTH past` by
              (map_every (fn pat => qpat_assum pat mp_tac)
                [`SUC i = LENGTH old_cuts`,`old_cuts = past ++ _`] >>
               POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`EL i old_cuts = _`,`old_cuts = past ++ _`,`i = LENGTH past`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[EL_APPEND_EQN]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`(ai,ei,qi) = (p,d,q)`,`SUC i = LENGTH old_cuts`,
            `EL (LENGTH old_cuts) cuts1 = _`,
            `EL q (THE (FLOOKUP ks' (p,d))) = AK1 bpath`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ]) >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`i = LENGTH old_cuts`,`EL i cuts1 = _`,`EL (LENGTH old_cuts) cuts1 = _`,
          `LENGTH cuts1 = SUC (LENGTH old_cuts)`] >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`FLOOKUP ks' (bpath,SUC d) = SOME ck`, `vq <= LENGTH ck`,
          `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`] >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[pairTheory.PAIR_EQ] >> rpt strip_tac >>
       qexistsl [`csf`,`callee`,`d`,`cs`,`NONE`,`NONE`,`[]`,`ck`] >>
       gvs[])) >>
     disch_then ACCEPT_TAC) >>
  `MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
        (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts1 = incoming0 ++ [d]` by
    (`MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
          (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) old_cuts = incoming0` by
       (simp[NoAsms,Abbr `incoming0`] >> irule LIST_EQ >> simp[NoAsms,EL_MAP] >>
        qx_gen_tac `i` >> strip_tac >>
        `?ai ds ei qi zi. EL i old_cuts = (ai,ds,ei,qi,zi)` by
          (POP_ASSUM_LIST (K all_tac) >> metis_tac[pairTheory.PAIR]) >>
        qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
           bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
             FLOOKUP acts ai = _ /\ _`
          (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then strip_assume_tac)) >>
        qpat_assum `!a value. FLOOKUP acts a = SOME value ==> _`
          (qspec_then `ai` (drule_then assume_tac)) >>
        map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
           [`EL i old_cuts = (ai,ds,ei,qi,zi)`,`FLOOKUP acts ai = SOME _`,
            `FLOOKUP acts' ai = SOME _`]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`MAP _ old_cuts = incoming0`,
        `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`,
        `Abbrev (cuts1 = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,MAP_APPEND]) >>
  `phi_prefix_length cbb.bb_instructions <= s1.vs_inst_idx` by
    (qpat_assum `phi_prefix_length (cps ++ cys) = phi_prefix_length cbb.bb_instructions`
       (SUBST1_TAC o SYM) >>
     qpat_assum `cbt.bb_instructions = cps ++ cys` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `cbe = NONE ==> (vq:num) = 0 /\ phi_prefix_length cbb.bb_instructions <= s1.vs_inst_idx /\
     s1.vs_inst_idx < LENGTH cps /\ vz =
       DROP (phi_prefix_length cbb.bb_instructions) (TAKE s1.vs_inst_idx cps)` by
    (disch_tac >>
     qpat_assum `cbe = NONE` (fn none =>
       qpat_assum `(IS_SOME cbe /\ _) \/ (cbe = NONE /\ _)`
         (mp_tac o SRULE [none]) >>
       qpat_assum `case cbe of NONE => _ | SOME _ => _` (mp_tac o SRULE [none])) >>
     qpat_assum `phi_prefix_length cbb.bb_instructions <= s1.vs_inst_idx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `IS_SOME cbe ==> vz = DROP (phi_prefix_length cbb.bb_instructions) cps ++ TAKE vq cxs` by
    (disch_tac >>
     qpat_assum `IS_SOME cbe` mp_tac >>
     qpat_assum `(IS_SOME cbe /\ _) \/ (cbe = NONE /\ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `cbe` >> simp[]) >>
  suspend "call_cut_finish"
QED
Resume dft_focus_packet_step_retained[call_cut_finish]:
  qexistsl [`cuts1`,`levels1`,`newM`,`newE`,`newK`,`ms_rest`,`es_rest`,`ks_rest`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
      bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
      FLOOKUP acts' ai = _ /\ FLOOKUP blocks' (ai,ei) = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rewrite_tac[pairTheory.pair_CASE_def] >>
     BETA_TAC >> disch_then ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  `MAX N (SUC d) <= fuel` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`N <= N'`,`SUC d <= N'`,`N' <= fuel`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.MAX_LE] >> decide_tac) >>
  qpat_assum `!F gs tail. MAX N (SUC d) <= F /\ _ ==> levels_ok F C7 levels1 _ _ root_sf _ [] 0 /\ _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `MAP _ cuts1 = incoming0 ++ [d]` (fn inc => rewrite_tac[inc]) >>
  Cases_on `SND (rooted_eval fuel C7 levels1 (root_entry with vs_gas_readings := gs ++ tail))` >>
    simp[NoAsms] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  FIRST [first_assum ACCEPT_TAC,
    (conj_tac >-
      (disch_tac >>
       qpat_assum `cbe = NONE ==> _` (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
       qpat_assum `_ ==> _ = s1 with vs_gas_readings := tail`
         (drule_all_then SUBST1_TAC) >>
       simp[NoAsms])) >>
    strip_tac >>
    qpat_assum `IS_SOME cbe ==> _` (drule_then assume_tac) >>
    qpat_assum `_ ==> (!op. MEM op inst'.inst_operands ==> _) /\ _`
      (drule_all_then ACCEPT_TAC)]
QED
Resume dft_focus_packet_step_retained[call_block_records]:
  map_every qx_gen_tac [`va`,`ve`,`vb`,`vt`,`vp`,`vx`,`vy`,`vr`,`vi`,`vh`,
     `vbody`,`vc`,`vf`,`vclosed`,`vrest`] >> disch_tac >>
  Cases_on `(va,ve) = (bpath,SUC d)`
  >- (qpat_x_assum `(va,ve) = _`
        (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS o SRULE []) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP blocks' (bpath,SUC d) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,vbody,vc,vf,vclosed,vrest)`,
         `FLOOKUP blocks' (bpath,SUC d) = SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`] >>
      simp[NoAsms] >> rpt disch_tac >>
      pop_assum (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
      map_every (fn pat => qpat_x_assum pat (SUBST_ALL_TAC o SYM))
        [`cbb = vb`,`cbt = vt`,`cps = vp`,`cxs = vx`,`cys = vy`,`crho = vr`,
         `cs = vi`,`SUC j = vh`,`cbe = vbody`,`OK s1 = vf`] >>
      map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
        [`vc = 0`,`vrest = NONE`] >>
      qpat_x_assum `~vclosed` (SUBST_ALL_TAC o EQF_INTRO) >>
      `SUC d <= N'` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry)`,
            `EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) = _`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
         drule_all native_trace_blocks_continuation >> simp[] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `EL (phi_prefix_length cbt.bb_instructions) cbt.bb_instructions = inst'` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`get_instruction cbt s1.vs_inst_idx = SOME inst'`,
            `s1 = sp with vs_inst_idx := _`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[venomInstTheory.get_instruction_def,AllCaseEqs()]) >>
      qexistsl [`csf`,`callee`,`d`,`cs`,`[SUC d]`,`NONE`,`NONE`,`sp`] >>
      simp[NoAsms] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      (conj_tac >-
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`cbb.bb_label = cs.vs_current_bb`, `lookup_block cs.vs_current_bb csf.fn_blocks = SOME cbb`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[])) >>
      (conj_tac >-
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`cbb.bb_label = cs.vs_current_bb`, `lookup_block cs.vs_current_bb callee.fn_blocks = SOME cbt`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[])) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      (conj_tac >-
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`EL (phi_prefix_length cbt.bb_instructions) cbt.bb_instructions = inst'`,
            `s1 = sp with vs_inst_idx := _`,
            `EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) = _`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss])) >>
      qpat_assum `case cbe of NONE => _ | SOME _ => _` mp_tac >>
      namedCases_on `cbe` ["", "vchildbody"]
      >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`Abbrev (has_body = _)`, `Abbrev (cm = _)`, `Abbrev (ce = _)`, `Abbrev (ck = _)`,
            `FLOOKUP ms' (bpath,SUC d) = SOME cm`, `FLOOKUP es' (bpath,SUC d) = SOME ce`,
            `FLOOKUP ks' (bpath,SUC d) = SOME ck`] >>
          POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def, SF CONJ_ss]) >>
      PairCases_on `vchildbody` >> simp[NoAsms] >> strip_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`s1 = sp with vs_inst_idx := _`, `cbb.bb_label = cs.vs_current_bb`,
         `eval_phis cs cbt.bb_instructions = OK sp`,
         `EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) = _`,
         `vchildbody0 = s1`,`vchildbody1 = SUC j`, `s1.vs_inst_idx = LENGTH cps`,
         `dft_remaining_inv csf cbb cxs s1`, `inst' = HD cys`,
         `!f C. FOLDR (dft_exec_cons f C) OK (DROP _ cps) _ = OK s1`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      gvs[] >> metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb]) >>
  qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
    (qspecl_then [`va`,`ve`] (drule_then assume_tac)) >>
  `FLOOKUP blocks (va,ve) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,vbody,vc,vf,vclosed,vrest)` by
    (qpat_assum `FLOOKUP blocks' (va,ve) = FLOOKUP blocks (va,ve)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
      FLOOKUP blocks (a,e) = _ ==> _`
    (qspecl_then [`va`,`ve`] (drule_then strip_assume_tac)) >>
  rename1 `FLOOKUP acts va = SOME (vsf,vtf,vinc,vent,vord,vres,vnr)` >>
  rename1 `eval_phis vi vt.bb_instructions = OK vsp` >>
  qexistsl [`vsf`,`vtf`,`vinc`,`vent`,`vord`,`vres`,`vnr`,`vsp`] >>
  (conj_tac >- first_assum (drule_then ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (`vh < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by
       (qpat_assum `vh <= j` mp_tac >>
        qpat_assum `j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
     qpat_assum `!h. h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) ==> _`
       (qspec_then `vh` (drule_then SUBST1_TAC)) >> first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (qpat_assum `if ve = SUC vinc then _ else _` mp_tac >>
     Cases_on `ve = SUC vinc`
     >- (qpat_assum `ve = SUC vinc` (fn th => simp[NoAsms,th])) >>
     qpat_assum `ve <> SUC vinc` (fn th => simp[NoAsms,th]) >> strip_tac >>
     qpat_assum `!key value. FLOOKUP blocks key = SOME value ==> _`
       (qspec_then `(va,ve-1)` (drule_then assume_tac)) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `case vbody of NONE => _ | SOME _ => _` mp_tac >>
  namedCases_on `vbody` ["", "voldbody"]
  >- (simp[NoAsms] >> rpt disch_tac >>
      `F` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`va = p`,`ve = d`, `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,OK s,F,NONE)`,
            `FLOOKUP blocks (va,ve) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,NONE,vc,vf,vclosed,vrest)`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
      first_assum CONTR_TAC) >>
  PairCases_on `voldbody` >> simp[NoAsms] >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (`voldbody1 < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by
       (qpat_assum `voldbody1 <= j` mp_tac >>
        qpat_assum `j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
     qpat_assum `!h. h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) ==> _`
       (qspec_then `voldbody1` (drule_then SUBST1_TAC)) >> first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (`FOLDR (dft_exec_cons (N' - ve) C8) OK (DROP (phi_prefix_length vt.bb_instructions) vp)
        (vsp with vs_inst_idx := phi_prefix_length vt.bb_instructions) =
      FOLDR (dft_exec_cons (N - ve) C8) OK (DROP (phi_prefix_length vt.bb_instructions) vp)
        (vsp with vs_inst_idx := phi_prefix_length vt.bb_instructions)` by
       (irule dft_packet_pseudo_fuel >> simp[EVERY_DROP]) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (gen_tac >> disch_tac >> first_assum irule >>
     qpat_assum `N' <= _` mp_tac >> qpat_assum `N <= N'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])) >>
  disch_tac >> first_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED
Resume dft_focus_packet_step_retained[call_records]:
  map_every qx_gen_tac [`a`,`e`,`cid`,`cq`,`ch`,`cb`,`done`,`cent`,`ret`] >> disch_tac >>
  Cases_on `(a,e,cid) = (p,d,inst.inst_id)`
  >- (qpat_assum `(a,e,cid) = (p,d,inst.inst_id)` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
      qpat_assum `FLOOKUP calls' (p,d,inst.inst_id) = SOME (q,j,s,TAKE cnt sched,cs,NONE)`
        (fn th => qpat_assum `(a,e,cid) = (p,d,inst.inst_id)`
          (fn eq => qpat_x_assum `FLOOKUP calls' (a,e,cid) = SOME (cq,ch,cb,done,cent,ret)`
                     (mp_tac o REWRITE_RULE [eq,th]))) >>
      simp[NoAsms] >> disch_then strip_assume_tac >>
      `SUC j > j` by simp[NoAsms] >>
      `LENGTH ps <= s.vs_inst_idx /\ s.vs_inst_idx - LENGTH ps = cnt` by simp[] >>
      `EL j (trace_blocks [] 0 N' C8 root_tf root_entry) = ((p,d,inst.inst_id),fn,inst,s)` by
        (qpat_assum `!h. h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) ==> _`
           (qspec_then `j` (drule_then SUBST1_TAC)) >> first_assum ACCEPT_TAC) >>
      `FLOOKUP acts' p = SOME (sf,fn,inc,entry,order,NONE,NONE)` by
        (qpat_assum `!a value. FLOOKUP acts a = SOME value ==> _` (irule) >> first_assum ACCEPT_TAC) >>
      `FLOOKUP blocks' (p,d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),cnt,OK s,F,NONE)` by
        (qpat_assum `!key value. FLOOKUP blocks key = SOME value ==> _` irule >> first_assum ACCEPT_TAC) >>
      `MEM bpath (GENLIST (\i. DROP i bpath) (SUC (LENGTH bpath)))` by
        (simp[NoAsms,MEM_GENLIST] >> qexists `0` >> simp[NoAsms]) >>
      map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
        [`q = cq`,`j = ch`,`s = cb`,`TAKE cnt sched = done`,`cs = cent`] >>
      map_every (fn pat => qpat_assum pat SUBST1_TAC)
        [`a = p`,`e = d`,`cid = inst.inst_id`,`EL q xs = inst`,
         `s.vs_inst_idx - LENGTH ps = cnt`] >>
      qpat_assum `bpath = (d,inst.inst_id)::p` (SUBST1_TAC o SYM) >>
      qexistsl [`sf`,`fn`,`inc`,`entry`,`order`,`NONE`,`NONE`,`bb`,`bt`,`ps`,`xs`,`ys`,
                `sched`,`hin`,`h0`,`be`,`hbe`,`cnt`,`OK s`,`F`,`NONE`,`csf`,`callee`,
                `[SUC d]`,`NONE`,`nm`,`ops`,`args`] >>
      map_every (fn pat => qpat_assum pat SUBST1_TAC)
        [`EL q xs = inst`,`s.vs_inst_idx - LENGTH ps = cnt`] >>
      simp[NoAsms] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      (conj_tac >-
        (gen_tac >> disch_tac >> first_assum irule >>
         qpat_assum `N' <= _` mp_tac >> qpat_assum `N <= N'` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP calls (a,e,cid) = SOME (cq,ch,cb,done,cent,ret)` by
    (qpat_assum `!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls' key = FLOOKUP calls key`
       (drule_then (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls (a,e,cid) = _ ==> _`
    (qspecl_then [`a`,`e`,`cid`] (drule_then strip_assume_tac)) >>
  `ch < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` by
    (qpat_assum `ch < j` mp_tac >>
     qpat_assum `j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `EL ch (trace_blocks [] 0 N' C8 root_tf root_entry) = ((a,e,cid),tf,c,cb)` by
    (qpat_assum `!h. h < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) ==> _`
       (qspec_then `ch` (drule_then SUBST1_TAC)) >> first_assum ACCEPT_TAC) >>
  qexistsl [`sf'`,`tf`,`inc'`,`entry'`,`order'`,`res`,`nrest`,`bb'`,`bt'`,`ps'`,`xs'`,`ys'`,
            `rho'`,`in_state`,`h0'`,`be'`,`hbe'`,`count'`,`front`,`closed`,`brest`,
            `csf'`,`ctf`,`child_order`,`child_res`,`child_rest`,`c`,`nm'`,`ops'`,`args'`] >>
  (conj_tac >- first_assum (drule_then ACCEPT_TAC)) >>
  (conj_tac >- first_assum (drule_then ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- simp[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (gen_tac >> disch_tac >> first_assum irule >>
     qpat_assum `N' <= _` mp_tac >> qpat_assum `N <= N'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum (drule_then ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `case ret of NONE => _ | SOME _ => _` mp_tac >>
  namedCases_on `ret` ["", "returned"]
  >- (simp[NoAsms] >> strip_tac >> simp[NoAsms,MEM_GENLIST] >>
      qpat_x_assum `MEM ((e,cid)::a) (GENLIST _ _)` mp_tac >>
      simp[NoAsms,MEM_GENLIST] >> strip_tac >>
      qpat_assum `bpath = (d,inst.inst_id)::p` SUBST1_TAC >>
      qexists `SUC i` >> simp[DROP]) >>
  PairCases_on `returned` >> simp[NoAsms] >> strip_tac >>
  `?u. child_rest = SOME u` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (qspec_then `(e,cid)::a` (drule_then strip_assume_tac)) >>
     qpat_assum `(child_res = NONE) <=> (child_rest = NONE)` mp_tac >>
     qpat_assum `child_res = SOME (IntRet returned0 returned1)` SUBST1_TAC >>
     Cases_on `child_rest` >> simp[NoAsms]) >>
  `run_blocks (N-e) C8 ctf cent = IntRet returned0 returned1` by
    (qpat_assum `!a sf tf inc entry order r8 u0. FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==> _`
       (qspec_then `(e,cid)::a` mp_tac) >>
     qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (csf',ctf,e,cent,child_order,child_res,child_rest)` mp_tac >>
     qpat_assum `child_res = SOME (IntRet returned0 returned1)` mp_tac >>
     qpat_assum `child_rest = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `trace_blocks ((e,cid)::a) e (N'-e) C8 ctf cent =
   trace_blocks ((e,cid)::a) e (N-e) C8 ctf cent` by
    (irule (cj 3 dftGasFromListTracePrefixTheory.trace_stable) >> simp[] >> decide_tac) >>
  pop_assum SUBST1_TAC >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `ch + SUC (LENGTH _) <= j` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> decide_tac
QED
Resume dft_focus_packet_step_retained[call_row_replay]:
  map_every qx_gen_tac [`va`,`ve`,`vb`,`vt`,`vp`,`vx`,`vy`,`vr`,`vi`,`vh`,
     `vbe`,`vbh`,`vc`,`vf`,`vclosed`,`vrest`,`vm`,`ves`,`vk`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `(va,ve) = (bpath,SUC d)`
  >- (qpat_x_assum `(va,ve) = _`
        (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS o SRULE []) >>
      `has_body` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP blocks' (bpath,SUC d) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,SOME (vbe,vbh),vc,vf,vclosed,vrest)`,
            `FLOOKUP blocks' (bpath,SUC d) = SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`,
            `cbe = if has_body then _ else _`] >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `has_body` >> simp[]) >>
      qpat_assum `FLOOKUP blocks' (bpath,SUC d) = SOME (cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`
        (fn th => qpat_assum `FLOOKUP blocks' (bpath,SUC d) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,SOME (vbe,vbh),vc,vf,vclosed,vrest)`
           (strip_assume_tac o SRULE [th])) >>
      map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC o SYM))
        [`cbb = vb`,`cps = vp`,`cxs = vx`,`crho = vr`] >>
      qpat_assum `vc = 0` SUBST_ALL_TAC >>
      map_every (fn (pat,eq) => qpat_assum pat (fn th => qpat_x_assum eq
        (SUBST_ALL_TAC o SYM o SRULE [th])))
        [(`FLOOKUP ms' (bpath,SUC d) = SOME cm`,`FLOOKUP ms' (bpath,SUC d) = SOME vm`),
         (`FLOOKUP es' (bpath,SUC d) = SOME ce`,`FLOOKUP es' (bpath,SUC d) = SOME ves`),
         (`FLOOKUP ks' (bpath,SUC d) = SOME ck`,`FLOOKUP ks' (bpath,SUC d) = SOME vk`)] >>
      `!cid. ALOOKUP obs (bpath,SUC d,cid) = NONE` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,root_order,NONE,NONE)`,
           `!a sf tf inc entry order res rest cid. _ ==> ~MEM (bpath,SUC d,cid) _`,
           `AK = _`, `LENGTH (AM []) = LENGTH (AK [])`,
           `PERM (MAP (\(key,slot). (key,THE slot)) (FILTER _ (ZIP (AK [],AM [])))) obs`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gen_tac >>
         simp[alistTheory.ALOOKUP_NONE,MEM_MAP,pairTheory.EXISTS_PROD] >>
         CCONTR_TAC >> gvs[] >>
         rename1 `MEM ((bpath,SUC d,cid),w) obs` >>
         drule dft_packet_observed_pair >>
         disch_then (qspecl_then [`(bpath,SUC d,cid)`,`w`] mp_tac) >>
         simp[MEM_ZIP] >> rpt strip_tac >>
         `MEM (bpath,SUC d,cid)
           (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) root_order))` by
           (rewrite_tac[MEM_EL] >> qexists `n` >> simp[]) >>
         qpat_assum `!a sf tf inc entry order res rest cid. _ ==> ~MEM (bpath,SUC d,cid) _`
           (qspecl_then [`[]`,`root_sf`,`root_tf`,`0`,`root_entry`,`root_order`,`NONE`,`NONE`,`cid`] mp_tac) >>
         simp[]) >>
      `!cid. FLOOKUP calls' (bpath,SUC d,cid) = NONE` by
        (gen_tac >>
         `(bpath,SUC d,cid) <> (p,d,inst.inst_id)` by simp[NoAsms] >>
         qpat_assum `!key. key <> (p,d,inst.inst_id) ==> FLOOKUP calls' key = _`
           (drule_then SUBST1_TAC) >>
         Cases_on `FLOOKUP calls (bpath,SUC d,cid)` >- simp[] >>
         PairCases_on `x` >>
         qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls (a,e,cid) = _ ==> _`
           (qspecl_then [`bpath`,`SUC d`,`cid`] (drule_then mp_tac)) >>
         qpat_assum `FLOOKUP acts bpath = NONE` (fn th => simp[NoAsms,th])) >>
      (conj_tac >-
        (simp[NoAsms,Abbr `cm`,Abbr `ce`,Abbr `ck`] >>
         qpat_assum `has_body` (fn th => simp[NoAsms,th]))) >>
      (conj_tac >- (simp[NoAsms,Abbr `cm`,Abbr `ce`] >>
                     qpat_assum `has_body` (fn th => simp[NoAsms,th]))) >>
      (conj_tac >- (simp[NoAsms,Abbr `cm`,Abbr `ck`] >>
                     qpat_assum `has_body` (fn th => simp[NoAsms,th]))) >>
      (conj_tac >- (simp[NoAsms,Abbr `cm`,Abbr `ce`,LIST_REL_EL_EQN] >>
                     qpat_assum `has_body` (fn th => simp[NoAsms,th,EL_GENLIST,COND_RAND]))) >>
      (conj_tac >- (simp[NoAsms,Abbr `cm`,Abbr `ck`,LIST_REL_EL_EQN] >>
                     qpat_assum `has_body` (fn th => simp[NoAsms,th,EL_GENLIST,COND_RAND]))) >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_tac >>
      conj_tac >- (
        qpat_assum `FLOOKUP acts' bpath = SOME (csf,callee,d,cs,[SUC d],NONE,NONE)`
          (fn th => qpat_x_assum `FLOOKUP acts' bpath = SOME (sf',tf,inc',entry',order',res,nrest)`
            (strip_assume_tac o SRULE [th])) >>
        simp[NoAsms,Abbr `cm`,Abbr `ce`,Abbr `ck`] >>
        map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
          [`has_body`, `csf = sf'`, `!cid. ALOOKUP obs (bpath,SUC d,cid) = NONE`,
           `!cid. FLOOKUP calls' (bpath,SUC d,cid) = NONE`] >>
        qx_gen_tac `r` >> disch_tac >>
        qpat_assum `r < LENGTH cxs` (fn th => simp[NoAsms,th,EL_GENLIST])) >>
      map_every qx_gen_tac [`fuel`,`k`,`kgss`,`tail`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      `N <= fuel` by
        (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
      qpat_assum `!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm re rk owner target incoming ent ord res nrest.
        FLOOKUP blocks' (a,e) = _ /\ _ ==> _`
        (qspecl_then [`bpath`,`SUC d`] (drule_all_then
          (qspec_then `tail` ACCEPT_TAC)))) >>
  `FLOOKUP blocks (va,ve) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,SOME (vbe,vbh),vc,vf,vclosed,vrest)` by
    (qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
       (qspecl_then [`va`,`ve`] (drule_then (SUBST1_TAC o SYM))) >> first_assum ACCEPT_TAC) >>
  `?oldm olde oldk. FLOOKUP ms_tab (va,ve) = SOME oldm /\
                   FLOOKUP es_tab (va,ve) = SOME olde /\
                   FLOOKUP ks_tab (va,ve) = SOME oldk` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks (va,ve) = SOME _`, `FDOM blocks = FDOM ms_tab`,
        `FDOM blocks = FDOM es_tab`, `FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     Cases_on `FLOOKUP ms_tab (va,ve)` >> Cases_on `FLOOKUP es_tab (va,ve)` >>
     Cases_on `FLOOKUP ks_tab (va,ve)` >> gvs[FLOOKUP_DEF]) >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> LENGTH ms = LENGTH xs /\ _`
    (qspecl_then [`va`,`ve`] (drule_all_then strip_assume_tac)) >>
  Cases_on `!r. r < plen ==> (va,ve) <> (DROP (SUC r) bpath,FST (EL r bpath))`
  >- (qpat_assum `!a e. (a,e) <> (bpath,SUC d) /\ _ ==> FLOOKUP ms' (a,e) = _ /\ _`
        (qspecl_then [`va`,`ve`] (drule_all_then strip_assume_tac)) >>
      map_every (fn (frame,old,new) => qpat_assum frame (fn fth =>
          qpat_assum old (fn oth => qpat_assum new
            (SUBST_ALL_TAC o SYM o SRULE [fth,oth]))))
        [(`FLOOKUP ms' (va,ve) = FLOOKUP ms_tab (va,ve)`,
          `FLOOKUP ms_tab (va,ve) = SOME oldm`,`FLOOKUP ms' (va,ve) = SOME vm`),
         (`FLOOKUP es' (va,ve) = FLOOKUP es_tab (va,ve)`,
          `FLOOKUP es_tab (va,ve) = SOME olde`,`FLOOKUP es' (va,ve) = SOME ves`),
         (`FLOOKUP ks' (va,ve) = FLOOKUP ks_tab (va,ve)`,
          `FLOOKUP ks_tab (va,ve) = SOME oldk`,`FLOOKUP ks' (va,ve) = SOME vk`)] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`owner`,`target`,`incoming`,`ent`,`ord`,`res`,`nrest`] >> disch_tac >>
      conj_tac >- (
        `va <> bpath` by
          (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
             FLOOKUP blocks (a,e) = _ ==> _`
             (qspecl_then [`va`,`ve`] (drule_then strip_assume_tac)) >>
           qpat_assum `FLOOKUP acts bpath = NONE` mp_tac >>
           qpat_assum `FLOOKUP acts va = SOME _` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> CCONTR_TAC >> gvs[]) >>
        `FLOOKUP acts va = SOME (owner,target,incoming,ent,ord,res,nrest)` by
          (qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = FLOOKUP acts a`
             (drule_then (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
        qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts va = _ ==> _`
          (drule_then (assume_tac o CONJUNCT1)) >>
        qx_gen_tac `r` >> disch_tac >>
        `!i. i < plen ==> (va,ve,(EL r vx).inst_id) <>
           (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath))` by
          (qx_gen_tac `i` >> disch_tac >>
           qpat_assum `!r. r < plen ==> (va,ve) <> _`
             (qspec_then `i` (drule_then mp_tac)) >>
           POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ]) >>
        qpat_assum `!va ve cid. _ ==> FLOOKUP calls' (va,ve,cid) = _ /\ _`
          (qspecl_then [`va`,`ve`,`(EL r vx).inst_id`] (drule_then (strip_assume_tac o GSYM))) >>
        qpat_assum `!r. r < LENGTH vx ==> _`
          (qspec_then `r` (drule_then mp_tac)) >>
        map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
          [`FLOOKUP calls (va,ve,(EL r vx).inst_id) = FLOOKUP calls' _`,
           `AM ((ve,(EL r vx).inst_id)::va) = AM1 _`,
           `AE ((ve,(EL r vx).inst_id)::va) = AE1 _`,
           `AK ((ve,(EL r vx).inst_id)::va) = AK1 _`]) >>
      map_every qx_gen_tac [`fuel`,`k`,`kgss`,`tail`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      `N <= fuel` by
        (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
      qpat_assum `!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm re rk owner target incoming ent ord res nrest.
        FLOOKUP blocks' (a,e) = _ /\ _ ==> _`
        (qspecl_then [`va`,`ve`] (drule_all_then
          (qspec_then `tail` ACCEPT_TAC)))) >>
  qpat_x_assum `~(!r. r < plen ==> _)` (strip_assume_tac o SRULE []) >>
  rename1 `i < plen` >>
  qpat_assum `!i. i < plen ==> ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0. _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  `vx = exs` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks (va,ve) = SOME _`,
        `FLOOKUP blocks (DROP (SUC i) bpath,FST (EL i bpath)) = SOME _`,
        `va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  qpat_x_assum `vx = exs` (SUBST_ALL_TAC o SYM) >>
  `vm = LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (DROP i bpath,f)))) (EL i ords))) (EL i inds) oldm /\
   ves = LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i bpath,f)))) (EL i ords))) (EL i inds) olde /\
   vk = LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i bpath,f)))) (EL i ords))) (EL i inds) oldk` by
    (let
       fun row_equation rule old new row =
         qpat_assum rule (qspecl_then [`i`,row] (mp_tac o cj 1)) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [old,new,`i < plen`,`va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]
     in
       conj_tac >- row_equation
         `!i rows. _ /\ FLOOKUP ms_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME rows ==> _`
         `FLOOKUP ms_tab (va,ve) = SOME oldm` `FLOOKUP ms' (va,ve) = SOME vm` `oldm` >>
       conj_tac >- row_equation
         `!i rows. _ /\ FLOOKUP es_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME rows ==> _`
         `FLOOKUP es_tab (va,ve) = SOME olde` `FLOOKUP es' (va,ve) = SOME ves` `olde` >>
       row_equation
         `!i rows. _ /\ FLOOKUP ks_tab (DROP (SUC i) bpath,FST (EL i bpath)) = SOME rows ==> _`
         `FLOOKUP ks_tab (va,ve) = SOME oldk` `FLOOKUP ks' (va,ve) = SOME vk` `oldk`
     end) >>
  `FLOOKUP acts va = SOME (osf,otf,oi,oen,EL (SUC i) ords,ores,orest)` by
    (map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
       [`va = DROP (SUC i) bpath`,`FLOOKUP acts (DROP (SUC i) bpath) = SOME _`]) >>
  `DROP i bpath = (ve,(EL (EL i inds) vx).inst_id)::va` by
    (qpat_assum `!i. i < plen ==> DROP i bpath = _`
       (qspec_then `i` (drule_then mp_tac)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`,
        `(EL (EL i inds) vx).inst_id = SND (EL i bpath)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  `?csf' ctf' ci cen cres crest.
    FLOOKUP acts' (DROP i bpath) = SOME (csf',ctf',ci,cen,EL i ords,cres,crest)` by
    (Cases_on `i = 0`
     >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`i = 0`,`EL 0 ords = [SUC d]`,`FLOOKUP acts' bpath = SOME _`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss]) >>
     `0 < i /\ i <= plen` by
       (map_every (fn pat => qpat_assum pat mp_tac) [`i <> 0`,`i < plen`] >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     `DROP i bpath <> bpath` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`0 < i`,`i <= plen`,`plen = LENGTH bpath`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        qpat_assum `DROP i bpath = bpath` (mp_tac o AP_TERM ``LENGTH : (num # num) list -> num``) >>
        simp[LENGTH_DROP] >> decide_tac) >>
     qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = FLOOKUP acts a`
       (drule_then SUBST1_TAC) >>
     qpat_assum `!i. 0 < i /\ i <= plen ==> ?osf otf oi oen ores orest. _`
       (qspec_then `i` (drule_all_then ACCEPT_TAC))) >>
  qabbrev_tac `newm = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (DROP i bpath,f)))) (EL i ords))` >>
  qabbrev_tac `newe = FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i bpath,f)))) (EL i ords))` >>
  qabbrev_tac `newk = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i bpath,f)))) (EL i ords))` >>
  `vm = LUPDATE newm (EL i inds) oldm /\
   ves = LUPDATE newe (EL i inds) olde /\
   vk = LUPDATE newk (EL i inds) oldk` by
    (simp[NoAsms,Abbr `newm`,Abbr `newe`,Abbr `newk`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `newm = AM1 (DROP i bpath) /\ newe = AE1 (DROP i bpath) /\ newk = AK1 (DROP i bpath)` by
    (qpat_assum `FLOOKUP acts' (DROP i bpath) = SOME _` (fn th =>
       simp[NoAsms,th,Abbr `AM1`,Abbr `AE1`,Abbr `AK1`,Abbr `newm`,Abbr `newe`,Abbr `newk`])) >>
  qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts va = _ ==> _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  `?lm rm le re lk rk.
     EL (EL i inds) oldm = lm ++ rm /\ newm = lm ++ FLAT cm ++ rm /\
     EL (EL i inds) olde = le ++ re /\ newe = le ++ FLAT ce ++ re /\
     EL (EL i inds) oldk = lk ++ rk /\ newk = lk ++ FLAT ck ++ rk /\
     LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
     LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk` by
    (Cases_on `i = 0`
     >- (qexistsl [`[]`,`[]`,`[]`,`[]`,`[]`,`[]`] >>
         `FLOOKUP calls (va,ve,(EL (EL i inds) vx).inst_id) = NONE` by
           (map_every (fn pat => qpat_assum pat mp_tac)
              [`i = 0`,`bpath = (d,inst.inst_id)::p`,
               `va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`,
               `(EL (EL i inds) vx).inst_id = SND (EL i bpath)`,
               `FLOOKUP calls (p,d,inst.inst_id) = NONE`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
         qpat_assum `!r. r < LENGTH vx ==> _`
           (qspec_then `EL i inds` (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2))) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`(EL (EL i inds) vx).inst_opcode = INVOKE`, `FLOOKUP calls (va,ve,_) = NONE`,
            `i = 0`,`EL 0 ords = [SUC d]`,
            `Abbrev (newm = _)`,`Abbrev (newe = _)`,`Abbrev (newk = _)`,
            `FLOOKUP ms' (bpath,SUC d) = SOME cm`,
            `FLOOKUP es' (bpath,SUC d) = SOME ce`,
            `FLOOKUP ks' (bpath,SUC d) = SOME ck`] >>
         POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[markerTheory.Abbrev_def]) >>
     `0 < i` by (qpat_assum `i <> 0` mp_tac >> simp[NoAsms,arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
     `i <= plen` by (qpat_assum `i < plen` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `!i. 0 < i /\ i < plen ==> ?ch b0 done child. _`
       (qspec_then `i` (drule_all_then strip_assume_tac)) >>
     qpat_assum `!i. 0 < i /\ i <= plen ==> ?osf otf oi oen ores orest. _`
       (qspec_then `i` (drule_all_then strip_assume_tac)) >>
     `?scall. FLOOKUP calls (va,ve,(EL (EL i inds) vx).inst_id) = SOME scall` by
       (map_every (fn pat => qpat_assum pat mp_tac)
           [`va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`,
            `(EL (EL i inds) vx).inst_id = SND (EL i bpath)`,
            `FLOOKUP calls (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath)) = SOME _`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss]) >>
     asm "call insertion at level" (qspec_then `i` (drule_all_then strip_assume_tac)) >>
     qpat_assum `!r. r < LENGTH vx ==> _`
       (qspec_then `EL i inds` (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2))) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`(EL (EL i inds) vx).inst_opcode = INVOKE`, `FLOOKUP calls (va,ve,_) = SOME scall`,
        `DROP i bpath = (ve,(EL (EL i inds) vx).inst_id)::va`,
        `FLOOKUP acts (DROP i bpath) = SOME (_,_,_,_,EL i ords,_,_)`,
        `AM = _`,`AE = _`,`AK = _`,
        `Abbrev (newm = _)`,`Abbrev (newe = _)`,`Abbrev (newk = _)`] >>
     rpt disch_tac >>
     rename1 `FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (DROP i bpath,f)))) (EL i ords)) = ml ++ mr` >>
     rename1 `FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (DROP i bpath,f)))) (EL i ords)) = elft ++ ergt` >>
     rename1 `FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (DROP i bpath,f)))) (EL i ords)) = kl ++ krgt` >>
     qexistsl [`ml`,`mr`,`elft`,`ergt`,`kl`,`krgt`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`(EL (EL i inds) vx).inst_opcode = INVOKE ==> _`,
        `(EL (EL i inds) vx).inst_opcode = INVOKE`, `FLOOKUP calls (va,ve,_) = SOME scall`,
        `DROP i bpath = (ve,(EL (EL i inds) vx).inst_id)::va`,
        `FLOOKUP acts (DROP i bpath) = SOME (_,_,_,_,EL i ords,_,_)`,
        `AM = _`,`AE = _`,`AK = _`,
        `Abbrev (newm = _)`,`Abbrev (newe = _)`,`Abbrev (newk = _)`,
        `FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (DROP i bpath,f)))) (EL i ords)) = ml ++ mr`,
        `FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (DROP i bpath,f)))) (EL i ords)) = elft ++ ergt`,
        `FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (DROP i bpath,f)))) (EL i ords)) = kl ++ krgt`,
        `FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (DROP i bpath,f)))) (EL i ords)) = ml ++ FLAT cm ++ mr`,
        `FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i bpath,f)))) (EL i ords)) = elft ++ FLAT ce ++ ergt`,
        `FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i bpath,f)))) (EL i ords)) = kl ++ FLAT ck ++ krgt`,
        `LENGTH ml = LENGTH elft`,`LENGTH ml = LENGTH kl`,
        `LENGTH mr = LENGTH ergt`,`LENGTH mr = LENGTH krgt`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[markerTheory.Abbrev_def]) >>
  `LENGTH newm = LENGTH newe /\ LENGTH newm = LENGTH newk` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`newm = lm ++ FLAT cm ++ rm`,`newe = le ++ FLAT ce ++ re`,
        `newk = lk ++ FLAT ck ++ rk`,`LENGTH (FLAT cm) = LENGTH (FLAT ce)`,
        `LENGTH (FLAT cm) = LENGTH (FLAT ck)`,`LENGTH lm = LENGTH le`,
        `LENGTH lm = LENGTH lk`,`LENGTH rm = LENGTH re`,`LENGTH rm = LENGTH rk`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  `ve IN set (EL (SUC i) ords)` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (qspec_then `va` (drule_then (qspec_then `ve` mp_tac o cj 7))) >>
     qpat_assum `FLOOKUP blocks (va,ve) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[FLOOKUP_DEF]) >>
  `!key. MEM key (FLAT ck) ==> ~MEM key (FLAT oldk)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!a sf tf inc entry order res rest key.
       FLOOKUP acts a = _ /\ MEM key (FLAT ck) ==> _`
       (qspec_then `va` (drule_all_then mp_tac)) >>
     qpat_assum `ve IN set (EL (SUC i) ords)` mp_tac >>
     qpat_assum `FLOOKUP ks_tab (va,ve) = SOME oldk` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 3 disch_tac >> strip_tac >>
     qpat_x_assum `~MEM key (FLAT (MAP _ _))` mp_tac >> simp[] >>
     simp[MEM_FLAT,MEM_MAP] >> qexists `FLAT oldk` >> simp[] >>
     qexists `ve` >> simp[]) >>
  `ALL_DISTINCT (FLAT (LUPDATE newk (EL i inds) oldk))` by
    (irule (cj 1 dftPacketCallKeyFreshnessTheory.dft_packet_call_key_row_replace) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (map_every (fn pat => qpat_assum pat mp_tac)
         [`LENGTH oldk = LENGTH oldm`,`LENGTH oldm = LENGTH vx`,`EL i inds < LENGTH vx`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss])) >>
     qexistsl [`FLAT ck`,`rk`,`lk`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  (conj_tac >- simp[LENGTH_LUPDATE]) >>
  (conj_tac >- simp[LENGTH_LUPDATE]) >>
  (conj_tac >- simp[LENGTH_LUPDATE]) >>
  (conj_tac >- (qpat_assum `vm = LUPDATE newm _ oldm` SUBST1_TAC >>
                qpat_assum `ves = LUPDATE newe _ olde` SUBST1_TAC >>
                irule EVERY2_LUPDATE_same >> simp[])) >>
  (conj_tac >- (qpat_assum `vm = LUPDATE newm _ oldm` SUBST1_TAC >>
                qpat_assum `vk = LUPDATE newk _ oldk` SUBST1_TAC >>
                irule EVERY2_LUPDATE_same >> simp[])) >>
  (conj_tac >- (qpat_assum `vk = LUPDATE newk _ oldk` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  map_every qx_gen_tac [`owner`,`target`,`incoming`,`ent`,`ord`,`res`,`nrest`] >> disch_tac >>
  conj_tac >- (
    `va <> bpath` by
      (map_every (fn pat => qpat_assum pat mp_tac)
         [`FLOOKUP acts bpath = NONE`,`FLOOKUP acts va = SOME _`] >>
       POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> CCONTR_TAC >> gvs[]) >>
    `FLOOKUP acts va = SOME (owner,target,incoming,ent,ord,res,nrest)` by
      (qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = FLOOKUP acts a`
         (drule_then (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
    qpat_assum `!sf tf inc entry order res nrest. FLOOKUP acts va = _ ==> _`
      (qspec_then `owner` (drule_then (assume_tac o CONJUNCT1))) >>
    qx_gen_tac `r` >> disch_tac >>
    Cases_on `r = EL i inds`
    >- (`?scall. FLOOKUP calls' (va,ve,(EL (EL i inds) vx).inst_id) = SOME scall` by
          (Cases_on `i = 0`
           >- (map_every (fn pat => qpat_assum pat mp_tac)
                 [`i = 0`,`bpath = (d,inst.inst_id)::p`,
                  `va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`,
                  `(EL (EL i inds) vx).inst_id = SND (EL i bpath)`,
                  `FLOOKUP calls' (p,d,inst.inst_id) = SOME _`] >>
               POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss]) >>
           `0 < i` by (qpat_assum `i <> 0` mp_tac >> simp[NoAsms,arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
           qpat_assum `!i. 0 < i /\ i < plen ==> ?ch b0 done child. _`
             (qspec_then `i` (drule_all_then strip_assume_tac)) >>
           qpat_assum `!key value. FLOOKUP calls key = SOME value ==> _`
             (drule_then assume_tac) >>
           map_every (fn pat => qpat_assum pat mp_tac)
             [`va = DROP (SUC i) bpath`,`ve = FST (EL i bpath)`,
              `(EL (EL i inds) vx).inst_id = SND (EL i bpath)`,
              `FLOOKUP calls' (DROP (SUC i) bpath,FST (EL i bpath),SND (EL i bpath)) = SOME _`] >>
           POP_ASSUM_LIST (K all_tac) >> simp[SF CONJ_ss]) >>
        map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
          [`r = EL i inds`,`(EL (EL i inds) vx).inst_opcode = INVOKE`,
           `FLOOKUP calls' (va,ve,(EL (EL i inds) vx).inst_id) = SOME scall`] >>
        map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
          [`vm = LUPDATE newm _ oldm`,`ves = LUPDATE newe _ olde`,`vk = LUPDATE newk _ oldk`,
           `newm = AM1 (DROP i bpath)`,`newe = AE1 (DROP i bpath)`,`newk = AK1 (DROP i bpath)`] >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`DROP i bpath = (ve,(EL (EL i inds) vx).inst_id)::va`,
           `LENGTH oldk = LENGTH oldm`,`LENGTH oldm = LENGTH vx`,
           `LENGTH olde = LENGTH oldm`,`EL i inds < LENGTH vx`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[EL_LUPDATE,SF CONJ_ss]) >>
    `ALL_DISTINCT (MAP (\x. x.inst_id) vx)` by
      (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> _`
         (qspecl_then [`va`,`ve`] (drule_then strip_assume_tac)) >>
       qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
         (qspec_then `va` (drule_then (assume_tac o cj 3))) >>
       qpat_assum `eb.bb_instructions = eps ++ vx` assume_tac >>
       qpat_assum `lookup_block eb.bb_label sf'.fn_blocks = SOME eb` assume_tac >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`lookup_block eb.bb_label sf'.fn_blocks = SOME eb`,
          `dft_fn_rel sf' _`, `eb.bb_instructions = eps ++ vx`] >>
       POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
       `wf_function sf' /\ MEM eb sf'.fn_blocks` by
         metis_tac[dft_fn_rel_def,venomExecProofsTheory.lookup_block_MEM] >>
       drule_all dftWfTheory.wf_fn_block_inst_ids_distinct >> simp[ALL_DISTINCT_APPEND]) >>
    `!k. k < plen ==> (va,ve,(EL r vx).inst_id) <>
       (DROP (SUC k) bpath,FST (EL k bpath),SND (EL k bpath))` by
      (qx_gen_tac `k` >> disch_tac >> strip_tac >>
       qpat_assum `(va,ve,(EL r vx).inst_id) = _` (strip_assume_tac o SRULE [pairTheory.PAIR_EQ]) >>
       `k = i` by
         (map_every (fn pat => qpat_assum pat (mp_tac o AP_TERM ``LENGTH : (num # num) list -> num``))
            [`va = DROP (SUC i) bpath`,`va = DROP (SUC k) bpath`] >>
          map_every (fn pat => qpat_assum pat mp_tac)
            [`plen = LENGTH bpath`,`k < plen`,`i < plen`] >>
          POP_ASSUM_LIST (K all_tac) >> simp[LENGTH_DROP] >> decide_tac) >>
       `r = EL i inds` by
         (map_every (fn pat => qpat_assum pat mp_tac)
            [`ALL_DISTINCT (MAP (\x. x.inst_id) vx)`,`r < LENGTH vx`,
             `EL i inds < LENGTH vx`,`k = i`,
             `(EL r vx).inst_id = SND (EL k bpath)`,
             `(EL (EL i inds) vx).inst_id = SND (EL i bpath)`] >>
          POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
          drule ALL_DISTINCT_EL_IMP >>
          disch_then (qspecl_then [`r`,`EL i inds`] mp_tac) >> simp[EL_MAP]) >>
       first_assum CONTR_TAC) >>
    qpat_assum `!va ve cid. _ ==> FLOOKUP calls' (va,ve,cid) = _ /\ _`
      (qspecl_then [`va`,`ve`,`(EL r vx).inst_id`] (drule_then (strip_assume_tac o GSYM))) >>
    qpat_assum `!r. r < LENGTH vx ==> _`
      (qspec_then `r` (drule_then mp_tac)) >>
    map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
      [`FLOOKUP calls (va,ve,(EL r vx).inst_id) = FLOOKUP calls' _`,
       `AM ((ve,(EL r vx).inst_id)::va) = AM1 _`,
       `AE ((ve,(EL r vx).inst_id)::va) = AE1 _`,
       `AK ((ve,(EL r vx).inst_id)::va) = AK1 _`,
       `vm = LUPDATE newm _ oldm`,`ves = LUPDATE newe _ olde`,`vk = LUPDATE newk _ oldk`] >>
    qpat_assum `r <> EL i inds` (fn th => simp[NoAsms,th,EL_LUPDATE])) >>
  map_every qx_gen_tac [`fuel`,`k`,`kgss`,`tail`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `N <= fuel` by
    (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `FLOOKUP blocks' (va,ve) =
       SOME (vb,vt,vp,vx,vy,vr,vi,vh,SOME (vbe,vbh),vc,vf,vclosed,vrest) /\
   FLOOKUP ms' (va,ve) = SOME vm /\
   FLOOKUP es' (va,ve) = SOME ves /\
   FLOOKUP ks' (va,ve) = SOME vk` by
    (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!a e rb rt rp rx ry rr ri rh rbe rbh rc rf rclosed rest rm re rk owner target incoming ent ord res nrest.
    FLOOKUP blocks' (a,e) = _ /\ _ ==> _`
    (qspecl_then [`va`,`ve`] (drule_all_then (qspec_then `tail` ACCEPT_TAC)))
QED
Resume dft_focus_packet_step_retained[call_historical_cut]:
  `FLOOKUP blocks (va,ve) = SOME (vb,vt,vp,vx,vy,vr,vi,vh,vbody,vc,vf,vclosed,vbr)` by
    (qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
      (qspecl_then [`va`,`ve`] (drule_then (SUBST1_TAC o SYM))) >> first_assum ACCEPT_TAC) >>
  `va <> bpath` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _`
        (qspecl_then [`va`,`ve`] (drule_then strip_assume_tac)) >>
     qpat_assum `FLOOKUP acts bpath = NONE` mp_tac >>
     qpat_assum `FLOOKUP acts va = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `FLOOKUP acts va = SOME (vsf,vtf,vinc,vent,vord,vres,vrest)` by
    (qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = _`
      (drule_then (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
  `IS_SOME vbody /\ vq < LENGTH vx /\
   vz = DROP (phi_prefix_length vb.bb_instructions) vp ++ TAKE vq vx /\
   EVERY (\i. ~is_terminator i.inst_opcode) (TAKE vq vx) /\
   (!r. r < vq /\ (EL r vx).inst_opcode = INVOKE ==> MEM r (TAKE vc vr))` by
    (qpat_assum `(IS_SOME vbody /\ _) \/ _` mp_tac >>
     qpat_assum `(va,ve) <> (bpath,SUC d)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[pairTheory.PAIR_EQ] >> metis_tac[]) >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest q z.
    FLOOKUP acts a = _ /\ FLOOKUP blocks (a,e) = _ /\ _ ==> ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (qspecl_then [`va`,`ve`] (mp_tac o
      ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] o ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO])) >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`vq`,`vz`] mp_tac) >>
  (impl_tac >- (disj1_tac >> simp[])) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi
     bei hbei counti fronti closedi resti later mi esi ki.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,
        SOME (bei,hbei),counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\ ALL_DISTINCT orderi /\
      ALL_DISTINCT (MAP (\inst. inst.inst_id) xsi) /\
      FLOOKUP ms_tab (ai,ei) = SOME mi /\ FLOOKUP es_tab (ai,ei) = SOME esi /\
      FLOOKUP ks_tab (ai,ei) = SOME ki /\
      LENGTH mi = LENGTH xsi /\ LENGTH esi = LENGTH xsi /\ LENGTH ki = LENGTH xsi /\
      qi < LENGTH xsi /\
      (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi)) /\
      (SUC i < LENGTH cuts ==>
        ?cid hh b0 done child ret csf ctf cinc corder cres crest.
          FST (EL (SUC i) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,hh,b0,done,child,ret) /\
          (EL qi xsi).inst_opcode = INVOKE /\ (EL qi xsi).inst_id = cid /\
          FLOOKUP acts ((ei,cid)::ai) = SOME (csf,ctf,cinc,child,corder,cres,crest) /\
          EL qi mi = AM ((ei,cid)::ai) /\ EL qi esi = AE ((ei,cid)::ai) /\
          EL qi ki = AK ((ei,cid)::ai))` by
    (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
     let val row = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,
                      `psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bodyi`,`counti`,`fronti`,
                      `closedi`,`resti`,`later`]
     in
       qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
                   bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
         (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then
            (List.foldr (fn (q,k) => qx_choose_then q k)
              (MAP_EVERY assume_tac o CONJUNCTS) row)))
     end >>
     `?bei hbei. bodyi = SOME (bei,hbei) /\ qi < LENGTH xsi /\
       (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi))` by
       (Cases_on `SUC i = LENGTH cuts`
        >- (qpat_assum `SUC i = LENGTH cuts` (fn guard =>
              qpat_assum `if SUC i = LENGTH cuts then _ else _`
                (strip_assume_tac o REWRITE_RULE [guard])) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`FLOOKUP blocks (ai,ei) = SOME _`,`FLOOKUP blocks (va,ve) = SOME _`,
               `ai = va`,`ei = ve`,`qi = vq`,`IS_SOME vbody`,`vq < LENGTH vx`,
               `!r. r < vq /\ _ ==> _`] >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[pairTheory.PAIR]) >>
        qpat_assum `SUC i <> LENGTH cuts` (fn guard =>
          qpat_assum `if SUC i = LENGTH cuts then _ else _`
            (strip_assume_tac o REWRITE_RULE [guard])) >>
        qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
          (qspecl_then [`ai`,`ei`,`cid`] (drule_then
            (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)))) >>
        `!r. MEM r done_at_call ==> MEM r (TAKE counti rhoi)` by
          (qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
             mp_tac >>
           qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,bodyi,_,_,_,_)` mp_tac >>
           qpat_assum `FLOOKUP calls (ai,ei,cid) = SOME (_,_,_,done_at_call,_,_)` mp_tac >>
           qhdtm_assum `dft_focus_packet_rel` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
           drule_all dft_packet_call_done_contained >> gvs[]) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`,
           `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,bodyi,_,_,_,_)`,
           `qi < LENGTH _`,`!r. r < qi /\ _ ==> MEM r done_at_call`,
           `!r. MEM r done_at_call ==> _`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
     qpat_assum `bodyi = SOME (bei,hbei)` SUBST_ALL_TAC >>
     `?mi esi ki. FLOOKUP ms_tab (ai,ei) = SOME mi /\
         FLOOKUP es_tab (ai,ei) = SOME esi /\ FLOOKUP ks_tab (ai,ei) = SOME ki` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
           `FDOM blocks = FDOM ks_tab`,`FLOOKUP blocks (ai,ei) = SOME _`] >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
     qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
                   _ ==> LENGTH ms = LENGTH xs /\ _`
       (qspecl_then [`ai`,`ei`] (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = SOME _ ==> _`
       (qspec_then `ai` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     `ALL_DISTINCT orderi` by
       (qpat_assum `orderi = GENLIST _ _` (SUBST1_TAC) >> simp[NoAsms,ALL_DISTINCT_GENLIST]) >>
     `ALL_DISTINCT (MAP (\inst. inst.inst_id) xsi)` by
       (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
                     FLOOKUP blocks (a,e) = _ ==> _`
          (qspecl_then [`ai`,`ei`] (drule_then mp_tac)) >>
        qpat_assum `FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)` SUBST1_TAC >>
        qpat_assum `dft_fn_rel sfi tfi` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        simp[] >> rpt strip_tac >>
        `wf_function sfi /\ MEM bbi sfi.fn_blocks` by
          metis_tac[dft_fn_rel_def,venomExecProofsTheory.lookup_block_MEM] >>
        `ALL_DISTINCT (MAP (\inst. inst.inst_id) bbi.bb_instructions)` by
          (irule dftWfTheory.wf_fn_block_inst_ids_distinct >> qexists `sfi` >> simp[]) >>
        pop_assum mp_tac >> simp[ALL_DISTINCT_APPEND]) >>
     qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,`psi`,
               `xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`hbei`,`counti`,`fronti`,`closedi`,
               `resti`,`later`,`mi`,`esi`,`ki`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH esi = LENGTH mi`,`LENGTH mi = LENGTH xsi`] >>
       POP_ASSUM_LIST (K all_tac) >> simp[])) >>
     (conj_tac >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ki = LENGTH mi`,`LENGTH mi = LENGTH xsi`] >>
       POP_ASSUM_LIST (K all_tac) >> simp[])) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     `SUC i <> LENGTH cuts` by
       (pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `SUC i <> LENGTH cuts` (fn guard =>
       qpat_assum `if SUC i = LENGTH cuts then _ else _`
         (strip_assume_tac o REWRITE_RULE [guard])) >>
     `FST (EL (SUC i) cuts) = (ei,cid)::ai` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`EL (SUC i) (MAP _ cuts) = (ei,cid)::ai`,`SUC i < LENGTH cuts`] >>
        POP_ASSUM_LIST (K all_tac) >> simp[EL_MAP] >>
        Cases_on `EL (SUC i) cuts` >> rename1 `_ = (path,payload)` >>
        PairCases_on `payload` >> simp[]) >>
     qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls _ = _ ==> _`
       (qspecl_then [`ai`,`ei`,`cid`] (drule_then mp_tac)) >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`FLOOKUP blocks (ai,ei) = SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,SOME (bei,hbei),counti,fronti,closedi,resti)`,
        `FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)`] >>
     simp[NoAsms] >> disch_then (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
     qpat_assum `!sf tf inc entry order res nrest.
         FLOOKUP acts ai = SOME _ ==> (!q. q < LENGTH xsi ==> _) /\ _`
       (fn rule => qpat_assum `FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti)`
         (mp_then Any (qspec_then `qi` assume_tac o CONJUNCT1) rule)) >>
     qexistsl [`h'`,`b0`,`done_at_call`,`child_entry`,`ret`,`csf'`,`ctf`,
               `ei`,`child_order`,`child_res`,`child_rest`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FST (EL (SUC i) cuts) = (ei,cid)::ai`,`(EL qi xsi).inst_id = cid`,
        `(EL qi xsi).inst_opcode = INVOKE`,`qi < LENGTH xsi`,
        `FLOOKUP calls (ai,ei,cid) = SOME (qi,h',b0,done_at_call,child_entry,ret)`,
        `FLOOKUP acts ((ei,cid)::ai) = SOME (csf',ctf,ei,child_entry,child_order,child_res,child_rest)`,
        `qi < LENGTH xsi ==> _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  `!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    (?sfi tfi inci enti orderi resi nresti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      orderi = ds ++ ei::later) /\
    (!f. MEM f ds ==> FLOOKUP blocks' (ai,f) = FLOOKUP blocks (ai,f)) /\
    (SUC i < LENGTH cuts ==> !cid.
      FST (EL (SUC i) cuts) = (ei,cid)::ai ==>
      FLOOKUP calls' (ai,ei,cid) = FLOOKUP calls (ai,ei,cid)) /\
    qi < LENGTH (THE (FLOOKUP ms' (ai,ei))) /\
    qi < LENGTH (THE (FLOOKUP es' (ai,ei))) /\
    qi < LENGTH (THE (FLOOKUP ks' (ai,ei))) /\
    (SUC i < LENGTH cuts ==>
      EL qi (THE (FLOOKUP ms' (ai,ei))) = AM1 (FST (EL (SUC i) cuts)) /\
      EL qi (THE (FLOOKUP es' (ai,ei))) = AE1 (FST (EL (SUC i) cuts)) /\
      EL qi (THE (FLOOKUP ks' (ai,ei))) = AK1 (FST (EL (SUC i) cuts))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))` by
    (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
     let val witnesses = [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,
                           `psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`hbei`,`counti`,
                           `fronti`,`closedi`,`resti`,`later`,`mi`,`esi`,`ki`]
     in
       qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
         bbi bti psi xsi ysi rhoi ini hi bei hbei counti fronti closedi resti later mi esi ki.
         _`
         (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] (drule_all_then
           (List.foldr (fn (q,k) => qx_choose_then q k)
             (MAP_EVERY assume_tac o CONJUNCTS) witnesses)))
     end >>
     let
       fun pieces (tab,out,row,indexed_row,up,frame) =
         qspecl_then [`acts`,`blocks`,`calls`,tab,`acts'`,`blocks'`,`calls'`,out,
                      `(csf,callee,d,cs,[SUC d],NONE,NONE)`,
                      `(cbb,cbt,cps,cxs,cys,crho,cs,SUC j,cbe,0,OK s1,F,NONE)`,
                      `(q,j,s,TAKE cnt sched,cs,NONE)`,`p`,`d`,`inst.inst_id`,
                      `bpath`,`plen`,`inds`,`ords`,`ai`,`ds`,`ei`,`qi`,`zi`,
                      `sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`,
                      `bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`SOME (bei,hbei)`,
                      `counti`,`fronti`,`closedi`,`resti`,row]
           mp_tac dftPacketCallPathGeometryTheory.dft_packet_call_historical_pieces >>
         (impl_tac >-
           (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
            (conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
            (conj_tac >- first_assum ACCEPT_TAC) >>
            (conj_tac >- simp[NoAsms]) >>
            (conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
            conj_tac
            >- (qx_gen_tac `r` >> disch_tac >>
                let val all = [`osf`,`otf`,`oi`,`oen`,`ores`,`orest`,`eb`,`tb`,`eps`,
                   `exs`,`eys`,`erho`,`ein`,`eh`,`ebe`,`ehbe`,`ecnt`,`eb0`,
                   `rm`,`re`,`rk`]
                in
                  qpat_assum `!i. i < plen ==>
                    ?osf otf oi oen ores orest eb tb eps exs eys erho ein eh ebe ehbe ecnt eb0 rm re rk. _`
                    (qspec_then `r` (drule_then (List.foldr (fn (q,k) => qx_choose_then q k)
                      (MAP_EVERY assume_tac o CONJUNCTS) all))) >>
                  qexistsl (List.take (all,17) @
                    [`OK eb0`,`F`,`NONE`,indexed_row])
                end >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
                first_assum ACCEPT_TAC) >>
            conj_tac
            >- (rpt strip_tac >> qpat_assum up (drule_all_then (ACCEPT_TAC o CONJUNCT1))) >>
            rpt strip_tac >> qpat_assum frame (drule_all_then (fn th =>
              FIRST (map ACCEPT_TAC (CONJUNCTS th)))))) >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS)
     in
       pieces (`ms_tab`,`ms'`,`mi`,`rm`,
         `!i rows. _ ==> FLOOKUP ms' _ = SOME (LUPDATE _ _ rows) /\ _`,
         `!a e. _ ==> FLOOKUP ms' (a,e) = _ /\ _`) >>
       pieces (`es_tab`,`es'`,`esi`,`re`,
         `!i rows. _ ==> FLOOKUP es' _ = SOME (LUPDATE _ _ rows) /\ _`,
         `!a e. _ ==> _ /\ FLOOKUP es' (a,e) = _ /\ _`) >>
       pieces (`ks_tab`,`ks'`,`ki`,`rk`,
         `!i rows. _ ==> FLOOKUP ks' _ = SOME (LUPDATE _ _ rows) /\ _`,
         `!a e. _ ==> _ /\ _ /\ FLOOKUP ks' (a,e) = _`)
     end >>
     let val child = [`ccid`,`chh`,`cb0`,`cdone`,`cchild`,`cret`,`csfi`,`ctfi`,
                      `cinci`,`cordi`,`cresi`,`cresti`]
         val get_child = qpat_assum `SUC i < LENGTH cuts ==> ?cid hh b0 done child ret
             csf ctf cinc corder cres crest. FST (EL (SUC i) cuts) = _ /\ _`
           (drule_then (List.foldr (fn (q,k) => qx_choose_then q k)
             (MAP_EVERY assume_tac o CONJUNCTS) child))
     in
       (conj_tac >- (qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`] >>
                     conj_tac >> first_assum ACCEPT_TAC)) >>
       (conj_tac >- (qx_gen_tac `f` >> disch_tac >>
         qpat_assum `!f. MEM f ds ==> FLOOKUP blocks' (ai,f) = FLOOKUP blocks (ai,f) /\ _`
           (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
       (conj_tac >- (disch_tac >> get_child >> qx_gen_tac `cid` >>
         qpat_assum `!key v. FLOOKUP calls key = SOME v ==> _`
           (qspec_then `(ai,ei,ccid)` (drule_then assume_tac)) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`FST (EL (SUC i) cuts) = (ei,ccid)::ai`,
            `FLOOKUP calls (ai,ei,ccid) = SOME (qi,chh,cb0,cdone,cchild,cret)`,
            `FLOOKUP calls' (ai,ei,ccid) = SOME (qi,chh,cb0,cdone,cchild,cret)`] >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])) >>
       map_every (fn (len,oldlen) => conj_tac >-
         (map_every (fn pat => qpat_assum pat mp_tac) [len,oldlen,`qi < LENGTH xsi`] >>
          POP_ASSUM_LIST (K all_tac) >> simp[]))
         [(`LENGTH (THE (FLOOKUP ms' (ai,ei))) = LENGTH mi`,`LENGTH mi = LENGTH xsi`),
          (`LENGTH (THE (FLOOKUP es' (ai,ei))) = LENGTH esi`,`LENGTH esi = LENGTH xsi`),
          (`LENGTH (THE (FLOOKUP ks' (ai,ei))) = LENGTH ki`,`LENGTH ki = LENGTH xsi`)] >>
       (conj_tac >- (disch_tac >> get_child >>
         qpat_assum `FST (EL (SUC i) cuts) = (ei,ccid)::ai` SUBST1_TAC >>
         let
           val old_child = `FLOOKUP acts ((ei,ccid)::ai) = SOME (_,_,_,_,cordi,_,_)`
           fun final_cell (cell,old_agg,new_agg,result) =
             qpat_assum old_agg (fn agg => qpat_assum old_child (fn lk =>
               qpat_assum cell (assume_tac o SRULE [agg,lk]))) >>
             qpat_assum result (qspec_then `ccid` (drule_all_then
               (MAP_EVERY assume_tac o CONJUNCTS))) >>
             qpat_assum new_agg (fn agg =>
               qpat_assum `FLOOKUP acts' ((ei,ccid)::ai) = SOME (_,_,_,_,cordi,_,_)`
                 (fn lk => simp[NoAsms,SRULE [markerTheory.Abbrev_def] agg,lk])) >>
             first_assum ACCEPT_TAC
         in
           conj_tac
           >- final_cell (`EL qi mi = AM _`,`AM = _`,`Abbrev (AM1 = _)`,
               `!cid h b0 done child ret sf tf inc entry ord res rest. _ ==> _ /\ _ /\ EL qi (THE (FLOOKUP ms' (ai,ei))) = _`) >>
           conj_tac
           >- final_cell (`EL qi esi = AE _`,`AE = _`,`Abbrev (AE1 = _)`,
               `!cid h b0 done child ret sf tf inc entry ord res rest. _ ==> _ /\ _ /\ EL qi (THE (FLOOKUP es' (ai,ei))) = _`) >>
           final_cell (`EL qi ki = AK _`,`AK = _`,`Abbrev (AK1 = _)`,
             `!cid h b0 done child ret sf tf inc entry ord res rest. _ ==> _ /\ _ /\ EL qi (THE (FLOOKUP ks' (ai,ei))) = _`)
         end)) >>
       map_every (fn pat => qpat_assum pat (fn th => simp[NoAsms,th]))
         [`FLOOKUP ms_tab (ai,ei) = SOME mi`, `FLOOKUP es_tab (ai,ei) = SOME esi`,
          `FLOOKUP ks_tab (ai,ei) = SOME ki`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC
     end) >>
  `cuts <> [] /\ FST (HD cuts) = []` by
    (qpat_assum `MAP _ cuts = REVERSE _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts`
     >- (strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     PairCases_on `h` >> strip_tac >> pop_assum (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_REVERSE,GENLIST_EQ_NIL,GENLIST_LAST,DROP_LENGTH_TOO_LONG]) >>
  let
    fun root_prefix (oldt,newt,agg,cut,oldrow,olddom,newdom,width,lookup,cell) =
      qpat_assum cut SUBST1_TAC >>
      Q.ISPECL_THEN [`acts'`,newt,oldt,`cuts`,agg] mp_tac
        dftPacketSelectedCutTransportTheory.dft_packet_selected_cut_prefix >>
      (impl_tac >-
       (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
        (conj_tac >- first_assum (ACCEPT_TAC o SRULE [markerTheory.Abbrev_def])) >>
        map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
        let val ws = [`sf1`,`tf1`,`inc1`,`entry1`,`order1`,`res1`,`rest1`,`later1`]
        in
          qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _) /\ _`
            (drule_all_then (CONJUNCTS_THEN2
              (List.foldr (fn (q,k) => qx_choose_then q k) strip_assume_tac ws)
              (MAP_EVERY assume_tac o CONJUNCTS))) >>
          qexistsl ws
        end >>
        qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
            bbi bti psi xsi ysi rhoi ini hi bei hbei counti fronti closedi resti later mi esi ki. _`
          (drule_all_then strip_assume_tac) >>
        qexists lookup >> ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
        (conj_tac >- (map_every (fn pat => qpat_assum pat mp_tac)
          [oldrow,olddom,newdom] >> POP_ASSUM_LIST (K all_tac) >>
          simp[FLOOKUP_DEF] >> metis_tac[])) >>
        (conj_tac >- (qpat_assum width mp_tac >> POP_ASSUM_LIST (K all_tac) >> simp[])) >>
        (conj_tac >- (disch_tac >> qpat_assum cell
          (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
          conj_tac >> first_assum ACCEPT_TAC)) >>
        first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
    val cells = `SUC i < LENGTH cuts ==> EL qi (THE (FLOOKUP ms' (ai,ei))) = _ /\ _`
  in
    `?rest. AM1 [] = Mcut ++ rest` by root_prefix
      (`ms_tab`,`ms'`,`AM1`,`Mcut = FLAT _`,`FLOOKUP ms_tab (ai,ei) = SOME _`,
       `FDOM blocks = FDOM ms_tab`,`FDOM ms' = _`,`qi < LENGTH (THE (FLOOKUP ms' (ai,ei)))`,
       `THE (FLOOKUP ms' (ai,ei))`,cells) >>
    `?rest. AE1 [] = Ecut ++ rest` by root_prefix
      (`es_tab`,`es'`,`AE1`,`Ecut = FLAT _`,`FLOOKUP es_tab (ai,ei) = SOME _`,
       `FDOM blocks = FDOM es_tab`,`FDOM es' = _`,`qi < LENGTH (THE (FLOOKUP es' (ai,ei)))`,
       `THE (FLOOKUP es' (ai,ei))`,cells) >>
    `?rest. AK1 [] = Kcut ++ rest` by root_prefix
      (`ks_tab`,`ks'`,`AK1`,`Kcut = FLAT _`,`FLOOKUP ks_tab (ai,ei) = SOME _`,
       `FDOM blocks = FDOM ks_tab`,`FDOM ks' = _`,`qi < LENGTH (THE (FLOOKUP ks' (ai,ei)))`,
       `THE (FLOOKUP ks' (ai,ei))`,cells)
  end >>
  (dftPacketSelectedCutTransportTheory.dft_packet_selected_cut_transport |>
     Q.GEN `gas_events_blocks` |> Q.ISPEC `gasEvents$gas_events_blocks` |>
     Q.SPECL [`acts`,`blocks`,`calls`] |>
     Q.GENL [`ms_tab'`,`es_tab'`,`ks_tab'`,`st`,`a`,`e`,`q`,`z`,`bb`,`sf`,`xs`] |>
     Q.SPECL [`ms'`,`es'`,`ks'`,`s`,`va`,`ve`,`vq`,`vz`,`vb`,`vsf`,`vx`] |>
     Q.GENL [`acts'`,`blocks'`,`calls'`,`body_entry`,`levels_ok`] |>
     Q.ISPECL_THEN [`acts'`,`blocks'`,`calls'`,`vbody`,
       `\fuel C lv paths incs root ent path (_:rat).
          levels_ok fuel C lv paths incs root ent path 0`]
       (mp_tac o BETA_RULE)) >>
  (impl_tac >-
   ((conj_tac >-
     (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi. _ ==> (?sfi tfi inci enti orderi resi nresti later. _) /\ _`
        (drule_all_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
      (conj_tac >-
       (map_every qx_gen_tac [`osf`,`otf`,`oinc`,`oentry`,`oord`,`ores`,`orest`,
          `obb`,`obt`,`ops0`,`oxs`,`oys`,`orho`,`oin`,`oh`,`obe`,`ocnt`,`ofront`,
          `oclosed`,`obrest`] >> strip_tac >>
        qpat_assum `FLOOKUP acts ai = SOME (osf,otf,oinc,oentry,oord,ores,orest)`
          (mk_asm "incoming cut act") >>
        `ai <> bpath` by
          (map_every (fn pat => qpat_assum pat mp_tac)
            [`FLOOKUP acts ai = SOME _`,`FLOOKUP acts bpath = NONE`] >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
        qpat_assum `!a. a <> bpath ==> FLOOKUP acts' a = _`
          (qspec_then `ai` (drule_then (fn th => rewrite_tac [th]))) >>
        `(ai,ei) <> (bpath,SUC d)` by
          (qpat_assum `ai <> bpath` mp_tac >> POP_ASSUM_LIST (K all_tac) >> simp[]) >>
        qpat_assum `!a e. (a,e) <> (bpath,SUC d) ==> FLOOKUP blocks' (a,e) = _`
          (qspecl_then [`ai`,`ei`] (drule_then (fn th => rewrite_tac [th]))) >>
        qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
            bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
          (drule_all_then strip_assume_tac) >>
        qexistsl [`oord`,`ores`,`orest`,`ocnt`,`ofront`,`oclosed`,`obrest`,`later`] >>
        (conj_tac >- first_assum ACCEPT_TAC) >>
        (conj_tac >- first_assum ACCEPT_TAC) >>
        qpat_assum `_ = ds ++ ei::later` mp_tac >>
        qpat_assum `FLOOKUP acts ai = SOME _` mp_tac >>
        asm "incoming cut act" mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[])) >>
      (conj_tac >- (rpt strip_tac >>
        qpat_assum `!f. MEM f ds ==> _` (drule_then (fn th => rewrite_tac [th])))) >>
      (conj_tac >-
       (strip_tac >> qx_gen_tac `cid` >> strip_tac >>
        qpat_assum `SUC i < LENGTH cuts ==> !cid. FST (EL (SUC i) cuts) = _ ==> _`
          (drule_then (qspec_then `cid` mp_tac)) >>
        qpat_assum `EL (SUC i) (MAP _ cuts) = (ei,cid)::ai` mp_tac >>
        qpat_assum `SUC i < LENGTH cuts` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[EL_MAP] >>
        Cases_on `EL (SUC i) cuts` >> rename1 `_ = (path,payload)` >>
        PairCases_on `payload` >> simp[])) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    map_every (fn (defpat,rempat) => conj_tac >-
      (qpat_assum defpat (mp_tac o SRULE [markerTheory.Abbrev_def]) >>
       qpat_assum rempat mp_tac >> POP_ASSUM_LIST (K all_tac) >>
       disch_tac >> disch_then SUBST_ALL_TAC >> metis_tac[]))
      [(`Abbrev (AM1 = _)`,`AM1 [] = Mcut ++ _`),
       (`Abbrev (AE1 = _)`,`AE1 [] = Ecut ++ _`),
       (`Abbrev (AK1 = _)`,`AK1 [] = Kcut ++ _`)] >>
    ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >-
      (qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti
          bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
          FLOOKUP acts ai = _ /\ FLOOKUP blocks (ai,ei) = _ /\ _ /\
          (if SUC i = LENGTH cuts then _ else _) /\ EL i levels = _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >> disch_then ACCEPT_TAC)) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> disch_tac >>
    qpat_assum `!F gs tail. N <= F /\ _ ==> levels_ok F C7 levels _ _ root_sf _ [] 0 /\ _`
      (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    POP_ASSUM_LIST (K all_tac) >>
    rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
    disch_then ACCEPT_TAC)) >>
  rewrite_tac [pairTheory.pair_CASE_def] >> BETA_TAC >>
  disch_then (qx_choose_then `new_mr` (qx_choose_then `new_er`
    (qx_choose_then `new_kr` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`new_mr`,`new_er`,`new_kr`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every (fn defpat => conj_tac >-
    (qpat_assum defpat (rewrite_tac o single o SRULE [markerTheory.Abbrev_def]) >>
     BETA_TAC >> first_assum ACCEPT_TAC))
    [`Abbrev (AM1 = _)`,`Abbrev (AE1 = _)`,`Abbrev (AK1 = _)`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  `N <= fuel` by
    (qpat_assum `N <= N'` mp_tac >> qpat_assum `N' <= fuel` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qpat_assum `!F gs tail. N <= F /\ _ ==> levels_ok F C7 levels _
    (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts)
    root_sf _ [] 0 /\ _` (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  `vbody <> NONE` by
    (qpat_assum `IS_SOME vbody` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `vbody` >> simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (mk_asm "historical outcome"))) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  asm_x "historical outcome" mp_tac >>
  qpat_assum `vbody <> NONE` (fn body =>
    qpat_assum `va <> bpath` (fn other =>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `SND (rooted_eval fuel C7 levels
        (root_entry with vs_gas_readings := gs ++ tail))` >>
      simp[body,other] >> strip_tac >> rpt conj_tac >>
      first_assum ACCEPT_TAC))
QED
Resume dft_focus_packet_step_retained[return]:
  gvs[] >> irule (dft_focus_packet_return_successor
    |> Q.INST [`packet` |-> `(j,obs)`] |> SRULE [pairTheory.FST]) >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >> simp[]
QED
Finalise dft_focus_packet_step_retained

Theorem dft_focus_packet_step:
  !(N:num) (C7:venom_context) C8 (root_sf:ir_function) (root_tf:ir_function)
    (root_entry:venom_state) packet
    (acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event,
      num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab : (((num # num) list # num), bytes32 option list list) fmap)
    (es_tab : (((num # num) list # num), (string # num) list list) fmap)
    (ks_tab : (((num # num) list # num), gas_event list list) fmap)
    rooted_eval p d cpl es0 raw_slots sites unused
    stk PG G tn fn inst s oms om hs h ev q8'.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    (inst.inst_opcode = GAS ==> s.vs_gas_readings <> []) /\
    joint_transition C8 (JointConfig stk PG G tn fn inst s oms om hs h) ev q8' ==>
    (?N' packet' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d'
      raw_slots' sites' unused'.
      dft_focus_packet_rel N' C7 C8 root_sf root_tf root_entry
        packet' acts' blocks' calls' ms_tab' es_tab' ks_tab' rooted_eval p' d'
        q8' raw_slots' sites' unused' /\
      LENGTH raw_slots' = LENGTH sites' /\
      PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0)) /\
    ( (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
       inst.inst_opcode = INVOKE) /\ ~in_revert_forward fn s ==>
      ?sf inc entry order bb bt ps xs ys rho in_state h0 be hbe count q z
        cuts levels Mcut Ecut.
        FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
        LAST order = d /\
        FLOOKUP blocks (p,d) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME(be,hbe),count,OK s,F,NONE) /\
        q = EL count rho /\ q < LENGTH xs /\ EL q xs = inst /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
          MEM r (TAKE count rho)) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid call_h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        LENGTH Mcut = LENGTH Ecut /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            C7 (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom C7 sf inst u /\
          ~in_revert_forward sf u /\
          (inv_memory_observation inst.inst_opcode ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
            u.vs_initial_fmp = s.vs_initial_fmp)))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SPEC_ALL dft_focus_packet_step_retained) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`fuel'`,`obs'`,`acts'`,`blocks'`,`calls'`,`ms_tab'`,`es_tab'`,
       `ks_tab'`,`p'`,`d'`,`raw_slots'`,`sites'`,`unused'`]
       (MAP_EVERY assume_tac o CONJUNCTS)) assume_tac) >>
  conj_tac
  >- (qexistsl_tac [`fuel'`,`(SUC (FST packet),obs')`,`acts'`,`blocks'`,`calls'`,
        `ms_tab'`,`es_tab'`,`ks_tab'`,`p'`,`d'`,`raw_slots'`,`sites'`,`unused'`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
