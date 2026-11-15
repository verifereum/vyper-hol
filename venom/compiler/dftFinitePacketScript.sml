Theory dftFinitePacket
Ancestors
  dftGasInvCrossingProbe dftGasFromListTraceDefs dftRunRel dftGasOracleDefs
  o1PassContract frameJointTransition unitMemInv list rich_list
  dftGasFromListRestore dftGasToListReplay gasEvents finite_map pred_set
  dftFinitePacketReachability dftGasFromListLookup dftContractGas

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

