Theory dftFinitePacket
Ancestors
  dftGasInvCrossingProbe dftGasFromListTraceDefs dftRunRel dftGasOracleDefs
  o1PassContract frameJointTransition unitMemInv list rich_list
  dftGasFromListRestore dftGasToListReplay gasEvents finite_map pred_set
  o1SafeUpto dftGasInvForwardActive stepWriteFootprintBase
  dftFinitePacketReachability dftGasFromListLookup dftContractGas
  dftPacketRootedAlignment dftPacketRefinementBoundary
  dftPacketNativeContinuation dftPacketNativeSlice
  dftPacketKeyMap dftPacketKeySubstitution dftPacketSlotRefine dftPacketCommonOracle

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
      bb.bb_instructions) = inst` by metis_tac[] >>
  `MEM ((p,d,inst.inst_id),sf,inst,u)
    (dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf
      (root_entry with vs_gas_readings := gs ++ tail))` by
    (qpat_x_assum `dftGasFromListTraceDefs$trace_blocks [] 0 fuel _ _ _ = _`
      (fn th => pure_rewrite_tac [th]) >> simp[]) >>
  `raw_reachable (root_entry with vs_gas_readings := gs ++ tail) C7 sf inst u` by
    (asm "reach" irule >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (drule_all dft_packet_cut_mem_inv >> simp[]) >>
  `active_inst sf inst u` by metis_tac[raw_reachable_active] >>
  `wf_function sf` by metis_tac[dft_fn_rel_def] >>
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
    metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
  `active_inst tf inst st` by
    (simp[contextCodegenRelTheory.active_inst_def] >>
     qexists_tac `bt` >>
     qpat_x_assum `get_instruction bt _ = SOME inst` mp_tac >>
     simp_tac (srw_ss()) [venomInstTheory.get_instruction_def] >>
     strip_tac >>
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

Theorem dft_packet_invoke_memory_order[local]:
  !x y. x.inst_opcode = INVOKE /\ inv_memory_observation y.inst_opcode ==>
    dft_must_order x y
Proof
  rpt gen_tac >> Cases_on `y.inst_opcode` >>
  simp[inv_memory_observation_def, dftScheduleOrderTheory.dft_must_order_def,
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

Theorem dft_packet_flat_length[local]:
  !ord. (!e. MEM e ord ==> LENGTH (keys e) = LENGTH (masks e)) ==>
    LENGTH (FLAT (MAP keys ord)) = LENGTH (FLAT (MAP masks ord))
Proof
  Induct >> simp[]
QED

Theorem dft_packet_flat_pair[local]:
  !ord. (!e. MEM e ord ==> LENGTH (keys e) = LENGTH (masks e)) /\
    MEM e ord /\ MEM kv (ZIP (keys e,masks e)) ==>
    MEM kv (ZIP (FLAT (MAP keys ord),FLAT (MAP masks ord)))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `LENGTH (keys h) = LENGTH (masks h)` by metis_tac[] >>
  `LENGTH (FLAT (MAP keys ord)) = LENGTH (FLAT (MAP masks ord))` by
    (irule dft_packet_flat_length >> metis_tac[]) >>
  simp[GSYM ZIP_APPEND] >> metis_tac[]
QED

Theorem dft_packet_flat_aligned[local]:
  !xs ys. LIST_REL (\x y. LENGTH x = LENGTH y) xs ys ==>
    LENGTH (FLAT xs) = LENGTH (FLAT ys)
Proof
  Induct >> Cases_on `ys` >> simp[] >> gvs[rich_listTheory.LENGTH_FLAT]
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
  metis_tac[dft_packet_flat_aligned]
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

Theorem dft_packet_row_pair[local]:
  !rows keyrows q.
    LIST_REL (\m k. LENGTH m = LENGTH k) rows keyrows /\
    q < LENGTH rows /\ MEM kv (ZIP (EL q keyrows,EL q rows)) ==>
    MEM kv (ZIP (FLAT keyrows,FLAT rows))
Proof
  Induct >> Cases_on `keyrows` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule dft_packet_flat_aligned >> disch_tac >>
  simp[GSYM ZIP_APPEND] >> Cases_on `q` >> gvs[] >> metis_tac[]
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

Theorem dft_packet_unflat_lookup[local]:
  !R rows keys.
    LIST_REL (\r k. LENGTH r = LENGTH k) rows keys /\
    LIST_REL R (FLAT keys) (FLAT rows) ==>
    LIST_REL (LIST_REL R) keys rows
Proof
  gen_tac >> Induct >> Cases_on `keys` >> simp[] >>
  rpt strip_tac >> gvs[LIST_REL_APPEND_EQ]
QED

Theorem dft_packet_flat_prefix_lookup[local]:
  !R ks ms. LIST_REL (LIST_REL R) ks ms ==>
    !q. LIST_REL R (FLAT (TAKE q ks)) (FLAT (TAKE q ms))
Proof
  gen_tac >> Induct >> Cases_on `ms` >> simp[] >>
  rpt gen_tac >> strip_tac >> gen_tac >> Cases_on `q` >> simp[] >>
  irule LIST_REL_APPEND_suff >> simp[]
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

Theorem dft_packet_pseudo_fuel[local]:
  !zs f g s. EVERY (\i. is_pseudo i.inst_opcode) zs ==>
    FOLDR (dft_exec_cons f C) OK zs s =
    FOLDR (dft_exec_cons g C) OK zs s
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `h.inst_opcode <> INVOKE` by
    (Cases_on `h.inst_opcode` >> gvs[venomInstTheory.is_pseudo_def]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def,
       venomExecSemanticsTheory.step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> simp[] >> metis_tac[]
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

Theorem dft_packet_call_done_contained[local]:
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
  cheat
QED

