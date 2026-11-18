Theory dftPacketPseudoNextClauses
Ancestors
  dftPacketPseudoCursor dftPacketPseudoNativeNext dftPacketPseudoFreshCut
  dftPacketPseudoKeyFreshness dftPacketExistingPathRows dftPacketExistingPathInsertion
  dftPacketPseudoHistoryFrame dftPacketPseudoHistoryCuts dftPacketPseudoHistoryReplay
  dftPacketFirstBodyObservation dftPacketFreshRow dftPacketEntryReplay
  dftPacketCallInsertionConservation dftPacketPseudoCurrentCutArrays
  dftGasFromListTraceDefs dftRunRel dftIndexedExec o1PassContract
  frameJointTransition unitMemInv gasEvents finite_map pred_set list rich_list
  venomInst venomState venomExecSemantics

Theorem dft_packet_pseudo_next_clauses:
  !(N:num) (C7:venom_context) C8 (root_sf:ir_function) root_tf
    (root_entry:venom_state)
    (acts:((num # num) list,ir_function # ir_function # num # venom_state #
      num list # exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),basic_block # basic_block #
      instruction list # instruction list # instruction list # num list #
      venom_state # num # (venom_state # num) option # num # exec_result #
      bool # bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    j obs AM AE AK row_eval plan_eval call_setup rooted_eval plan_ok levels_ok
    p d fn inst s sf inc entry order bb bt ps xs ys rho in_state h0
    k l g u s1 i1.
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  MEM root_sf C7.ctx_functions /\ root_tf = dft_fn root_sf /\
  dft_fn_rel root_sf root_tf /\
  strict_dom_vars_defined root_sf root_entry /\
  fn_reachable root_sf root_entry.vs_current_bb /\
  ctx_labels_bound C7 root_entry.vs_labels /\
  ctx_labels_bound C8 root_entry.vs_labels /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  LENGTH obs <= LENGTH root_entry.vs_gas_readings /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  root_entry.vs_gas_readings = MAP SND obs ++ s.vs_gas_readings /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (AK []) /\
  LENGTH (AM []) = LENGTH (AE []) /\ LENGTH (AM []) = LENGTH (AK []) /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\
  FDOM blocks = FDOM ks_tab /\
  (?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
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
        FLOOKUP calls (parent,e,cid) = SOME (q,h,b0,done_at_call,entry,ret))) /\
  (!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      MEM e order /\ e <= N /\ h0 <= j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb /\
      bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM row_order (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) row_order ys /\
      strict_dom_vars_defined sf in_state /\
      fn_reachable sf in_state.vs_current_bb /\
      ctx_labels_bound C7 in_state.vs_labels /\ ctx_labels_bound C8 in_state.vs_labels /\
      eval_phis in_state bt.bb_instructions = OK sp /\
      EL h0 (trace_blocks [] 0 N C8 root_tf root_entry) =
        ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
          EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
          sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then in_state = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc (pr:num) pu.
          FLOOKUP blocks (a,e-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK in_state,T,SOME pu) /\
          ~in_state.vs_halted) /\
      count <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_entry of
        NONE => a = p /\ e = d /\ count = 0 /\ front = OK s /\
          FLOOKUP ms_tab (a,e) = SOME [] /\ FLOOKUP es_tab (a,e) = SOME [] /\
          FLOOKUP ks_tab (a,e) = SOME []
      | SOME (be,hbe) =>
          hbe <= j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\
          EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
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
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
  FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\ LAST order = d /\
  FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho,in_state,h0,NONE,0,OK s,F,NONE) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bt /\
  get_instruction bt s.vs_inst_idx = SOME inst /\
  phi_prefix_length bt.bb_instructions <= s.vs_inst_idx /\ s.vs_inst_idx < LENGTH ps /\
  FOLDR (dft_exec_cons (N-d) C8) OK
    (DROP (phi_prefix_length bt.bb_instructions) (TAKE s.vs_inst_idx ps))
    ((case eval_phis in_state bt.bb_instructions of OK sp => sp | other => in_state)
      with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s /\
  k = s.vs_inst_idx /\ l = phi_prefix_length ps /\
  is_pseudo inst.inst_opcode /\ step_inst g C8 inst s = OK u /\
  s1 = u with vs_inst_idx := SUC k /\ get_instruction bt s1.vs_inst_idx = SOME i1 /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
      h < j /\ EL h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,cid),tf,c,b0) /\
      LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME c /\
      (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
        (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
      done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done_at_call /\
      FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
      (case ret of
        NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
      | SOME (ir,child_out,caller_post) =>
          child_res = SOME (IntRet ir child_out) /\
          bind_outputs c.inst_outputs ir.iret_values
            (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
          h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) <= j /\
          MEM q (TAKE count rho))) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
      done_at_call = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
        (gas_events_block (F-e) C owner
          (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
         FOLDR (dft_exec_cons (F-e) C) OK z (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (row_eval F C owner row s),SND (row_eval F C owner row s))
    | other => (es,other)) ([],OK entry) plan) /\
  call_setup = (\C c s.
    case decode_invoke c of NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) => case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee => case eval_operands ops s of NONE => Error "invoke: undefined argument"
        | SOME args => case setup_callee callee args s of NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call). case r of
      OK ent => (prior ++ FST (plan_eval F C sf.fn_name plan ent),
        case SND (plan_eval F C sf.fn_name plan ent) of
          OK caller => (case call of NONE => OK caller | SOME c => call_setup C c caller)
        | other => other)
    | other => (prior,other)) ([],OK entry) levels) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\ MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
      else LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s. r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\ (0 < r ==> ~s.vs_halted))) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\ LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\ FST (HD levels) = root_fn /\
    (!i sf plan call. i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent. rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then ?c nm ops bb e z.
        call = SOME c /\ LAST plan = (bb,e,z) /\
        c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
        lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
        EL (SUC i) incoming = e /\ EL (SUC i) paths = (e,c.inst_id)::EL i paths
      else call = NONE))) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks ==>
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\ ALL_DISTINCT (FLAT ks) /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      (!q. q < LENGTH xs ==>
        ((EL q xs).inst_opcode = GAS ==>
          EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
          EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\ EL q ks = [(a,e,(EL q xs).inst_id)]) /\
        ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
          EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
        ((EL q xs).inst_opcode = INVOKE ==>
          (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
            NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
          | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
              EL q ess = AE ((e,(EL q xs).inst_id)::a) /\
              EL q ks = AK ((e,(EL q xs).inst_id)::a)))) /\
      (!F k kgss tail.
        N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) = gas_events_block (F-e) C7 sf.fn_name
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
            (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))))) /\
  (!a e cid q h b0 done_at_call child_entry ret
      bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u. N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee args b0)) /\
  (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      be hbe count r8 u0 ms ess ks.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks ==>
    terminates r8 /\ PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess = gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail) = OK v \/
            ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_block a e (F-e) C7 sf
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
  (!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    terminates r8 /\ LENGTH (AM a) = LENGTH (AE a) /\ LENGTH (AM a) = LENGTH (AK a) /\
    PERM (MAP THE (FILTER IS_SOME (AM a)) ++ u0) entry.vs_gas_readings /\
    (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
      EVERY IS_SOME (AM a) /\ u0 = v.vs_gas_readings) /\
    (!F. N <= F ==> run_blocks (F-inc) C8 tf entry = r8 /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM a) gs ==>
        (?extra. AE a = gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
            gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE a /\
            residual_result tail r8 (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
        (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
            ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_blocks a inc (F-inc) C7 sf
            (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs))))) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  (!bb bt ps xs ys rho in_state h0 be hbe count sf inc entry order.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s,F,NONE) /\
    inv_memory_observation inst.inst_opcode ==>
    EL (EL count rho) xs = inst /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count rho) xs) /\
    (!q. q < EL count rho /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho))) /\
  (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest q z.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    ((IS_SOME body_entry /\ q < LENGTH xs /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
      (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho))) \/
     (body_entry = NONE /\ a = p /\ e = d /\ q = 0 /\
      z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps))) ==>
    ?cuts levels Mcut Ecut Kcut mr er kr.
      MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
      LENGTH cuts = LENGTH levels /\
      (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
        ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
          ini hi bei counti fronti closedi resti later.
          FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
          FLOOKUP blocks (ai,ei) =
            SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
          orderi = ds ++ ei::later /\
          (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z else
            ?cid h b0 done_at_call child_entry ret.
              EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
              FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
              qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
              zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
              EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
              (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
          EL i levels = (sfi,
            MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
              (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++ [(bbi,ei,zi)],
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
      (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
        levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
          (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
            (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
          root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
        (?extra. Ecut = FST (rooted_eval F C7 levels
          (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
        (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
          OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
            u.vs_gas_readings = tail /\
            (?before after. trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,(EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
              trace_gas before = ZIP (Kcut,gs)) /\
            (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
              (Ecut,OK (u with vs_gas_readings := tail'))) /\
            (body_entry = NONE ==> u with vs_gas_readings := s.vs_gas_readings = s) /\
            (a = p /\ e = d /\ IS_SOME body_entry /\ inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
              (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
              u.vs_initial_fmp = s.vs_initial_fmp)
        | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
            gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))) ==>
  ?blocks1 ms_out es_out ks_out AM1 AE1 AK1 inds orders.
    blocks1 = blocks |+ ((p,d),
      (bb,bt,ps,xs,ys,rho,in_state,h0,
       if SUC k < LENGTH ps then NONE else SOME (s1,SUC j),0,OK s1,F,NONE)) /\
    LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
    (!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti.
      FLOOKUP acts (DROP i p) = SOME (sfi,tfi,inci,enti,EL i orders,resi,nresti)) /\
    (!i. i < LENGTH p ==> ?call_h b0 done child_entry.
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,call_h,b0,done,child_entry,NONE)) /\
    ((SUC k < LENGTH ps /\ ms_out = ms_tab /\ es_out = es_tab /\ ks_out = ks_tab) \/
     (SUC k = LENGTH ps /\ ?mt et kt.
       LENGTH mt = SUC (LENGTH p) /\ LENGTH et = SUC (LENGTH p) /\ LENGTH kt = SUC (LENGTH p) /\
       EL 0 mt = ms_tab |+ ((p,d),GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs)) /\
       EL 0 et = es_tab |+ ((p,d),GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs)) /\
       EL 0 kt = ks_tab |+ ((p,d),GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(p,d,(EL q xs).inst_id)] else []) (LENGTH xs)) /\
       ms_out = EL (LENGTH p) mt /\ es_out = EL (LENGTH p) et /\ ks_out = EL (LENGTH p) kt /\
       (!i. i < LENGTH p ==>
         EL (SUC i) mt = EL i mt |+ ((DROP (SUC i) p,FST (EL i p)),
           LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP (EL i mt) (DROP i p,e)))) (EL i orders)))
             (EL i inds) (THE (FLOOKUP (EL i mt) (DROP (SUC i) p,FST (EL i p))))) /\
         EL (SUC i) et = EL i et |+ ((DROP (SUC i) p,FST (EL i p)),
           LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP (EL i et) (DROP i p,e)))) (EL i orders)))
             (EL i inds) (THE (FLOOKUP (EL i et) (DROP (SUC i) p,FST (EL i p))))) /\
         EL (SUC i) kt = EL i kt |+ ((DROP (SUC i) p,FST (EL i p)),
           LUPDATE (FLAT (MAP (\e. FLAT (THE (FLOOKUP (EL i kt) (DROP i p,e)))) (EL i orders)))
             (EL i inds) (THE (FLOOKUP (EL i kt) (DROP (SUC i) p,FST (EL i p)))))))) /\
    AM1 = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AE1 = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AK1 = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    SUC j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,i1.inst_id),fn,i1,s1) /\
    trace_gas (TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry)) = obs /\
    root_entry.vs_gas_readings = MAP SND obs ++ s1.vs_gas_readings /\
    s1.vs_gas_readings = s.vs_gas_readings /\
    ALL_DISTINCT (AK1 []) /\ LENGTH (AM1 []) = LENGTH (AE1 []) /\ LENGTH (AM1 []) = LENGTH (AK1 []) /\
    PERM (MAP (\(key,slot). (key,THE slot))
      (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK1 [],AM1 [])))) obs /\
    (!g0. PERM (MAP THE (FILTER IS_SOME (AM [])) ++ s.vs_gas_readings) g0 ==>
      PERM (MAP THE (FILTER IS_SOME (AM1 [])) ++ s1.vs_gas_readings) g0) /\
    FDOM blocks1 = FDOM blocks /\ FDOM blocks1 = FDOM ms_out /\
    FDOM blocks1 = FDOM es_out /\ FDOM blocks1 = FDOM ks_out /\
    (!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==>
      ?sf tf inc entry order res nrest sp.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        MEM e order /\ e <= N /\ h0 <= SUC j /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
        lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb /\
        bt.bb_label = bb.bb_label /\
        bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
        EVERY (\x. is_pseudo x.inst_opcode) ps /\ EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
        EVERY (\x. ~is_pseudo x.inst_opcode) ys /\ EVERY inst_shape_ok bb.bb_instructions /\
        LENGTH xs = LENGTH ys /\ PERM row_order (COUNT_LIST (LENGTH xs)) /\
        LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
          from_block [EL q xs] y) row_order ys /\
        strict_dom_vars_defined sf in_state /\ fn_reachable sf in_state.vs_current_bb /\
        ctx_labels_bound C7 in_state.vs_labels /\ ctx_labels_bound C8 in_state.vs_labels /\
        eval_phis in_state bt.bb_instructions = OK sp /\
        EL h0 (trace_blocks [] 0 N C8 root_tf root_entry) =
          ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
            EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
            sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
        (if e = SUC inc then in_state = entry else
          ?pb pt pps pxs pys prho pin ph pbe pc (pr:num) pu.
            FLOOKUP blocks1 (a,e-1) =
              SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK in_state,T,SOME pu) /\ ~in_state.vs_halted) /\
        count <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
        (case body_entry of
          NONE => a = p /\ e = d /\ count = 0 /\ front = OK s1 /\
            FLOOKUP ms_out (a,e) = SOME [] /\ FLOOKUP es_out (a,e) = SOME [] /\ FLOOKUP ks_out (a,e) = SOME []
        | SOME (be,hbe) =>
            hbe <= SUC j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
            dft_remaining_inv sf bb xs be /\
            EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
            FOLDR (dft_exec_cons (N-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
              (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
            (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE count ys) be = front) /\
            (closed ==> count = LENGTH ys /\ terminates front /\
              (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
        (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
        (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME bt /\ get_instruction bt s1.vs_inst_idx = SOME i1 /\
    (if SUC k < LENGTH ps then
      phi_prefix_length bt.bb_instructions <= s1.vs_inst_idx /\ s1.vs_inst_idx < LENGTH ps /\
      FOLDR (dft_exec_cons (N-d) C8) OK
        (DROP (phi_prefix_length bt.bb_instructions) (TAKE s1.vs_inst_idx ps))
        ((case eval_phis in_state bt.bb_instructions of OK sp => sp | other => in_state)
          with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1
    else s1.vs_inst_idx = LENGTH ps /\ 0 < LENGTH ys /\ i1 = EL 0 ys) /\
    (!a e cid q h b0 done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
      ?sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
        be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks1 (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
        q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
        h < SUC j /\ EL h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,cid),tf,c,b0) /\
        LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME c /\
        (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
          (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
        done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done_at_call /\
        FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
        decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
        eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
        (case ret of
          NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
        | SOME (ir,child_out,caller_post) => child_res = SOME (IntRet ir child_out) /\
            bind_outputs c.inst_outputs ir.iret_values
              (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
            h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) <= SUC j /\
            MEM q (TAKE count rho))) /\
    (!k. k < LENGTH p ==>
      ?sf tf inc entry order bb bt ps xs ys rho in_state h0 be hbe count
        q h b0 done_at_call child_entry cid e a.
        a = DROP (SUC k) p /\ (e,cid) = EL k p /\
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
        FLOOKUP blocks1 (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
        FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
        done_at_call = TAKE count rho /\ b0.vs_inst_idx = LENGTH ps + count /\
        get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
    (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_out (a,e) = SOME ms /\ FLOOKUP es_out (a,e) = SOME ess /\
      FLOOKUP ks_out (a,e) = SOME ks ==>
      LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
      LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
      LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\ ALL_DISTINCT (FLAT ks) /\
      (!sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
        (!q. q < LENGTH xs ==>
          ((EL q xs).inst_opcode = GAS ==>
            EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
            EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\ EL q ks = [(a,e,(EL q xs).inst_id)]) /\
          ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
            EL q ms = [] /\ EL q ess = [] /\ EL q ks = []) /\
          ((EL q xs).inst_opcode = INVOKE ==>
            (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
              NONE => EL q ms = [] /\ EL q ess = [] /\ EL q ks = []
            | SOME call => EL q ms = AM1 ((e,(EL q xs).inst_id)::a) /\
                EL q ess = AE1 ((e,(EL q xs).inst_id)::a) /\
                EL q ks = AK1 ((e,(EL q xs).inst_id)::a)))) /\
        (!F k kgss tail.
          N <= F /\ k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
          (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho)) /\
          LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
          (?extra. FLAT (TAKE k ess) = gas_events_block (F-e) C7 sf.fn_name
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
              (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
            (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
                (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
              gas_events_block (F-e) C7 sf.fn_name
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
                (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))))) /\
    (!a e cid q h b0 done_at_call child_entry ret
        bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) /\
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP ms_out (a,e) = SOME ms ==>
      !F kgss tail u. N <= F /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
        (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee args b0)) /\
    (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
        be hbe count r8 u0 ms ess ks.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
      FLOOKUP ms_out (a,e) = SOME ms /\ FLOOKUP es_out (a,e) = SOME ess /\
      FLOOKUP ks_out (a,e) = SOME ks ==>
      terminates r8 /\ PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
      (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
        EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
      (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
        (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
          (?extra. FLAT ess = gas_events_block (F-e) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) ==>
            terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
              gas_events_block (F-e) C7 sf.fn_name
                <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
              residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
                (be with vs_gas_readings := gs ++ tail)))) /\
          (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
            trace_gas (trace_block a e (F-e) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) /\
    (!a sf tf inc entry order r8 u0.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
      terminates r8 /\ LENGTH (AM1 a) = LENGTH (AE1 a) /\ LENGTH (AM1 a) = LENGTH (AK1 a) /\
      PERM (MAP THE (FILTER IS_SOME (AM1 a)) ++ u0) entry.vs_gas_readings /\
      (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==>
        EVERY IS_SOME (AM1 a) /\ u0 = v.vs_gas_readings) /\
      (!F. N <= F ==> run_blocks (F-inc) C8 tf entry = r8 /\
        (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM1 a) gs ==>
          (?extra. AE1 a = gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
            terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
              gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = AE1 a /\
              residual_result tail r8 (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))) /\
          (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
            trace_gas (trace_blocks a inc (F-inc) C7 sf
              (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK1 a,gs))))) /\
    (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) ==>
      !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
        ?h b0 done_at_call child_entry ir child_out caller_post.
          FLOOKUP calls (a,e,(EL q xs).inst_id) =
            SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
    (!bb bt ps xs ys rho in_state h0 be hbe count sf inc entry order.
      FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
      FLOOKUP blocks1 (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,OK s1,F,NONE) /\
      inv_memory_observation i1.inst_opcode ==>
      EL (EL count rho) xs = i1 /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count rho) xs) /\
      (!q. q < EL count rho /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count rho))) /\
    (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest q z.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks1 (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      ((IS_SOME body_entry /\ q < LENGTH xs /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho))) \/
       (body_entry = NONE /\ a = p /\ e = d /\ q = 0 /\
        z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s1.vs_inst_idx ps))) ==>
      ?cuts levels Mcut Ecut Kcut mr er kr.
        MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks1 (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
            EL i levels = (sfi,
              MAP (\f. case THE (FLOOKUP blocks1 (ai,f)) of
                (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                  (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++ [(bbi,ei,zi)],
              if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_out (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_out (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_out (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_out (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_out (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_out (ai,ei))))) cuts) /\
        AM1 [] = Mcut ++ mr /\ AE1 [] = Ecut ++ er /\ AK1 [] = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
            (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
              (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
            root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
          (?extra. Ecut = FST (rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after. trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                before ++ [((a,e,(EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                  bb.bb_instructions)).inst_id),sf,
                  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
                trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
                (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==> u with vs_gas_readings := s1.vs_gas_readings = s1) /\
              (a = p /\ e = d /\ IS_SOME body_entry /\ inv_memory_observation i1.inst_opcode /\ EL q xs = i1 ==>
                (!op. MEM op i1.inst_operands ==> eval_operand op u = eval_operand op s1) /\
                u.vs_initial_fmp = s1.vs_initial_fmp)
          | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))))
Proof
  rpt gen_tac >> strip_tac >>
  map_every (fn v => qpat_x_assum v (mk_asm "evaluators"))
    [`row_eval = _`,`plan_eval = _`,`call_setup = _`,`rooted_eval = _`,
     `plan_ok = _`,`levels_ok = _`] >>
  qpat_x_assum `AM = _` (mk_asm "AMeq") >>
  qpat_x_assum `AE = _` (mk_asm "AEeq") >>
  qpat_x_assum `AK = _` (mk_asm "AKeq") >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
    (mk_asm "activations") >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _`
    (mk_asm "block_records") >>
  qpat_x_assum `!k. k < LENGTH p ==> _` (mk_asm "parents") >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==> _`
    (mk_asm "call_records") >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\ _ ==> _`
    (mk_asm "rows") >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_) ==> !q. _`
    (mk_asm "old_completed_calls") >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME _ /\ FLOOKUP blocks (a,e) = SOME _ /\ FLOOKUP ms_tab (a,e) = SOME ms ==> _`
    (mk_asm "old_caller_Q") >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0 be hbe count r8 u0 ms ess ks.
    FLOOKUP acts a = SOME _ /\ FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,_,_,_,T,_) /\ _ ==> _`
    (mk_asm "old_closed_row") >>
  qpat_x_assum `!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME (_,_,_,_,_,SOME r8,SOME u0) ==> _`
    (mk_asm "old_closed_activation") >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest q z.
    FLOOKUP acts a = SOME _ /\ FLOOKUP blocks (a,e) = SOME _ /\ _ ==>
    ?cuts levels Mcut Ecut Kcut mr er kr. _` (mk_asm "old_rooted_cuts") >>
  rpt (qpat_x_assum `!x. _` (mk_asm "history")) >>
  `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` by simp[] >>
  drule_all dft_packet_pseudo_native_next >> strip_tac >>
  asm "block_records" drule >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\ EVERY (\i. i.inst_opcode <> PHI) ys` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY (\i. ~is_pseudo i.inst_opcode) xs`,
        `EVERY (\i. ~is_pseudo i.inst_opcode) ys`] >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >>
     metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bt.bb_instructions = l /\ phi_prefix_length bb.bb_instructions = l` by
    simp[dft_phi_prefix_append] >>
  `inst = EL k ps` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`get_instruction bt s.vs_inst_idx = SOME inst`,
        `bt.bb_instructions = ps ++ ys`,`k = s.vs_inst_idx`,
        `s.vs_inst_idx < LENGTH ps`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[get_instruction_def,EL_APPEND1]) >>
  `inst.inst_opcode <> INVOKE` by
    (qpat_assum `is_pseudo inst.inst_opcode` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `inst.inst_opcode` >>
     simp[is_pseudo_def]) >>
  `step_inst (N-d) C8 (EL k ps) s = OK u` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`step_inst g C8 inst s = OK u`,`inst = EL k ps`,
        `inst.inst_opcode <> INVOKE`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[step_inst_non_invoke]) >>
  `l <= k /\ k < LENGTH ps /\ s.vs_inst_idx = k` by simp[] >>
  `FOLDR (dft_exec_cons (N-d) C8) OK (DROP l (TAKE k ps))
    (sp with vs_inst_idx := l) = OK s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FOLDR (dft_exec_cons (N-d) C8) OK _ _ = OK s`,
        `eval_phis in_state bt.bb_instructions = OK sp`,
        `phi_prefix_length bt.bb_instructions = l`,`k = s.vs_inst_idx`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  drule_all dft_packet_pseudo_cursor_split >> strip_tac >>
  qpat_x_assum `FLOOKUP acts p = SOME _`
    (fn th => qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`
      (fn eq => mp_tac (REWRITE_RULE [eq] th))) >>
  simp_tac pure_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  asm "activations" drule >> strip_tac >>
  `wf_function sf /\ fn_inst_wf sf` by
    (qpat_assum `dft_fn_rel sf fn` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[dft_fn_rel_def]) >>
  `MEM bb sf.fn_blocks` by
    (qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_inst_wf sf`,`MEM bb sf.fn_blocks`] >>
     rpt (pop_assum kall_tac) >> simp[venomWfTheory.fn_inst_wf_def,EVERY_MEM] >>
     metis_tac[]) >>
  `eval_phis in_state ps = OK sp` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_phis in_state bt.bb_instructions = OK sp`,
        `bt.bb_instructions = ps ++ ys`,
        `EVERY (\i. i.inst_opcode <> PHI) ys`] >>
     rpt (pop_assum kall_tac) >> simp[dft_eval_phis_append]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`wf_function sf`,`MEM bb sf.fn_blocks`] >>
     rpt (pop_assum kall_tac) >>
     simp[venomWfTheory.wf_function_def,venomWfTheory.fn_inst_ids_distinct_def] >>
     rpt strip_tac >> drule venomWfPropsTheory.all_distinct_flat_map_member >>
     disch_then drule >> simp[]) >>
  `bb.bb_label = in_state.vs_current_bb` by
    (qpat_assum `lookup_block in_state.vs_current_bb sf.fn_blocks = SOME bb` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `!i lab. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
      ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      i.inst_opcode <> CODECOPY /\ MEM (Label lab) i.inst_operands ==>
      lab IN FDOM in_state.vs_labels` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ctx_labels_bound C7 in_state.vs_labels`,`MEM sf C7.ctx_functions`,
        `MEM bb sf.fn_blocks`] >>
     rpt (pop_assum kall_tac) >>
     simp[ctx_labels_bound_def,fn_insts_def,fn_insts_blocks_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    ((qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `i.inst_opcode` >>
     simp[is_pseudo_def,is_terminator_def] >> (gvs[EVERY_MEM, is_pseudo_def, is_terminator_def]))) >>
  `FOLDR (dft_exec_cons (N-d) C8) OK (DROP l (TAKE (SUC k) ps))
    (sp with vs_inst_idx := l) = OK s1` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FOLDR (dft_exec_cons (N-d) C8) OK (DROP l (TAKE k ps)) _ = OK s`,
        `step_inst (N-d) C8 (EL k ps) s = OK u`,
        `s1 = u with vs_inst_idx := SUC k`,`s.vs_inst_idx = k`,
        `l <= k`,`k < LENGTH ps`,`EVERY (\i. ~is_terminator i.inst_opcode) ps`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `DROP l (TAKE (SUC k) ps) = DROP l (TAKE k ps) ++ [EL k ps]` by
       (simp[TAKE_SUC_BY_TAKE,SNOC_APPEND,DROP_APPEND,LENGTH_TAKE] >>
        `l - k = 0` by decide_tac >> simp[]) >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (DROP l (TAKE k ps)) /\
      ~is_terminator (EL k ps).inst_opcode` by
       gvs[EVERY_DROP,EVERY_TAKE,EVERY_EL] >>
     asm_rewrite_tac[FOLDR_APPEND] >>
     simp[Once dft_exec_prefix_continue] >> simp[dft_exec_cons_def]) >>
  `SUC k = LENGTH ps ==> dft_remaining_inv sf bb xs s1` by
    (strip_tac >>
     `FOLDR (dft_exec_cons (N-d) C8) OK (DROP (phi_prefix_length ps) ps)
       (sp with vs_inst_idx := phi_prefix_length ps) = OK s1` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`FOLDR (dft_exec_cons (N-d) C8) OK (DROP l (TAKE (SUC k) ps)) _ = OK s1`,
           `SUC k = LENGTH ps`,`l = phi_prefix_length ps`] >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[TAKE_LENGTH_ID]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`bb.bb_instructions = ps ++ xs`,
        `EVERY (\i. is_pseudo i.inst_opcode) ps`,
        `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,
        `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`,
        `EVERY inst_wf bb.bb_instructions`,`bb.bb_label = in_state.vs_current_bb`,
        `strict_dom_vars_defined sf in_state`,
        `!i lab. MEM i bb.bb_instructions /\ _ ==> lab IN FDOM in_state.vs_labels`,
        `eval_phis in_state ps = OK sp`,
        `FOLDR (dft_exec_cons (N-d) C8) OK (DROP (phi_prefix_length ps) ps) _ = OK s1`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule_all dft_packet_pseudo_initialized >> simp[]) >>
  qabbrev_tac `inds = GENLIST (\i. FST (THE (FLOOKUP calls
    (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p)` >>
  qabbrev_tac `orders = GENLIST (\i. (FST o SND o SND o SND o SND)
    (THE (FLOOKUP acts (DROP i p)))) (SUC (LENGTH p))` >>
  `LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p)` by
    simp[Abbr `inds`,Abbr `orders`] >>
  `!i. i < LENGTH p ==> ?call_h b0 done child_entry.
    FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
      SOME (EL i inds,call_h,b0,done,child_entry,NONE)` by
    (gen_tac >> strip_tac >>
     asm "parents" (qspec_then `i` mp_tac) >>
     qpat_assum `i < LENGTH p` mp_tac >>
     qpat_assum `Abbrev (inds = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[Abbr `inds`]) >>
  `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti.
    FLOOKUP acts (DROP i p) =
      SOME (sfi,tfi,inci,enti,EL i orders,resi,nresti)` by
    (gen_tac >> strip_tac >> Cases_on `i = 0`
     >- (qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` mp_tac >>
         qpat_assum `i = 0` mp_tac >> qpat_assum `Abbrev (orders = _)` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[Abbr `orders`] >>
         metis_tac[]) >>
     asm "parents" (qspec_then `i-1` mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`i <= LENGTH p`,`i <> 0`,`Abbrev (orders = _)`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `i-1 < LENGTH p /\ SUC (i-1) = i` by decide_tac >>
     gvs[Abbr `orders`] >> metis_tac[]) >>
  `!a e. (a,e) IN FDOM blocks ==> ?ms ess ks.
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
        `FDOM blocks = FDOM ks_tab`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[FLOOKUP_DEF]) >>
  `!i. i < LENGTH p ==> ?ms ess ks.
    FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
    FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME ess /\
    FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks /\
    EL i inds < LENGTH ms /\ EL i inds < LENGTH ess /\ EL i inds < LENGTH ks` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?call_h b0 done child_entry. _` drule >>
     strip_tac >> asm "call_records" drule >> strip_tac >>
     `?ms ess ks.
       FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
       FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME ess /\
       FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks` by
       (qpat_assum `!a e. (a,e) IN FDOM blocks ==> _` irule >>
        qpat_assum `FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) = SOME _` mp_tac >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
           `FDOM blocks = FDOM ks_tab`] >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[flookup_thm]) >>
     asm "rows" (fn th => drule_all (cj 1 th)) >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 2 th)) >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 3 th)) >> strip_tac >>
     qexistsl [`ms`,`ess`,`ks`] >> simp[]) >>
  `!i. i < LENGTH p ==> ?ms.
    FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
    EL i inds < LENGTH ms` by
    (qpat_assum `!i. i < LENGTH p ==> ?ms ess ks. _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule (pp (Pos (el 4)) dft_packet_existing_path_rows) >>
  disch_then (qspecl_then [`orders`,`d`,
    `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs)`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `mt` (qx_choose_then `ms_new` strip_assume_tac)) >>
  `!i. i < LENGTH p ==> ?ess.
    FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME ess /\
    EL i inds < LENGTH ess` by
    (qpat_assum `!i. i < LENGTH p ==> ?ms ess ks. _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule (pp (Pos (el 4)) dft_packet_existing_path_rows) >>
  disch_then (qspecl_then [`orders`,`d`,
    `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs)`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `et` (qx_choose_then `es_new` strip_assume_tac)) >>
  `!i. i < LENGTH p ==> ?ks.
    FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks /\
    EL i inds < LENGTH ks` by
    (qpat_assum `!i. i < LENGTH p ==> ?ms ess ks. _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule (pp (Pos (el 4)) dft_packet_existing_path_rows) >>
  disch_then (qspecl_then [`orders`,`d`,
    `GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(p,d,(EL q xs).inst_id)] else []) (LENGTH xs)`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `kt` (qx_choose_then `ks_new` strip_assume_tac)) >>
  `!i. i <= LENGTH p ==> ALL_DISTINCT (EL i orders)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _` drule >>
     strip_tac >> asm "activations" drule >> strip_tac >>
     qpat_assum `EL i orders = GENLIST _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     once_asm_rewrite_tac[] >> simp[ALL_DISTINCT_GENLIST]) >>
  `EL 0 orders = order` by
    (qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` mp_tac >>
     qpat_assum `Abbrev (orders = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[Abbr `orders`]) >>
  `?ds. EL 0 orders = ds ++ [d]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EL 0 orders = order`,`order <> []`,`LAST order = d`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qexists_tac `FRONT order` >> metis_tac[APPEND_FRONT_LAST]) >>
  `!i. i < LENGTH p ==> MEM (FST (EL i p)) (EL (SUC i) orders)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?call_h b0 done child_entry. _` drule >>
     strip_tac >> asm "call_records" drule >> strip_tac >>
     qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _`
       (qspec_then `SUC i` mp_tac) >>
     (impl_tac >- (qpat_assum `i < LENGTH p` mp_tac >>
       rpt (pop_assum kall_tac) >> decide_tac)) >> strip_tac >>
     qpat_assum `FLOOKUP acts (DROP (SUC i) p) = SOME (_,_,_,_,EL (SUC i) orders,_,_)`
       (fn th => asm "activations" (mp_tac o C MATCH_MP th)) >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!e. MEM e (EL (SUC i) orders) <=> _`,
        `FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) = SOME _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[flookup_thm]) >>
  `!a e. (a,e) IN FDOM blocks ==> ?mr er kr.
    FLOOKUP ms_tab (a,e) = SOME mr /\ FLOOKUP es_tab (a,e) = SOME er /\
    FLOOKUP ks_tab (a,e) = SOME kr /\
    LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr kr` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a e. (a,e) IN FDOM blocks ==> ?ms ess ks. _` drule >>
     disch_then (qx_choose_then `mr` (qx_choose_then `er` (qx_choose_then `kr` strip_assume_tac))) >>
     `?bval. FLOOKUP blocks (a,e) = SOME bval` by
       (qpat_assum `(a,e) IN FDOM blocks` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[FLOOKUP_DEF]) >>
     PairCases_on `bval` >>
     Cases_on `bval8`
     >- (asm "block_records" drule >> simp_tac std_ss [] >>
         strip_tac >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP ms_tab (a,e) = SOME []`,`FLOOKUP es_tab (a,e) = SOME []`,
            `FLOOKUP ks_tab (a,e) = SOME []`] >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         qexistsl [`[]`,`[]`,`[]`] >> simp[]) >>
     PairCases_on `x` >>
     asm "rows" (fn th => drule_all (cj 1 th)) >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 2 th)) >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 3 th)) >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 4 th)) >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 5 th)) >> strip_tac >>
     qexistsl [`mr`,`er`,`kr`] >> asm_rewrite_tac[]) >>
  `!i. i <= LENGTH p ==>
    AM (DROP i p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (DROP i p,f)))) (EL i orders)) /\
    AE (DROP i p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (DROP i p,f)))) (EL i orders)) /\
    AK (DROP i p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (DROP i p,f)))) (EL i orders))` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _` drule >>
     strip_tac >>
     map_every (fn name => asm name mp_tac) ["AMeq","AEeq","AKeq"] >>
     qpat_assum `FLOOKUP acts (DROP i p) = SOME (_,_,_,_,EL i orders,_,_)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[]) >>
  `!i f. i <= LENGTH p /\ MEM f (EL i orders) ==>
    ?mr er kr. FLOOKUP ms_tab (DROP i p,f) = SOME mr /\
      FLOOKUP es_tab (DROP i p,f) = SOME er /\ FLOOKUP ks_tab (DROP i p,f) = SOME kr /\
      LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
      LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
      LIST_REL (\x y. LENGTH x = LENGTH y) mr kr` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a e. (a,e) IN FDOM blocks ==> ?mr er kr. _` irule >>
     qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _` drule >>
     strip_tac >> asm "activations" (fn th => drule (cj 7 th)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`MEM f (EL i orders)`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!i. i < LENGTH p ==> ?mr er kr.
    FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
    FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME er /\
    FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME kr /\
    EL i inds < LENGTH mr /\ EL i inds < LENGTH er /\ EL i inds < LENGTH kr /\
    EL (EL i inds) mr = AM (DROP i p) /\
    EL (EL i inds) er = AE (DROP i p) /\
    EL (EL i inds) kr = AK (DROP i p)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?call_h b0 done child_entry. _` drule >>
     strip_tac >> asm "call_records" drule >> strip_tac >>
     qpat_assum `!i. i < LENGTH p ==> ?ms ess ks. _` drule >> strip_tac >>
     asm "rows" (fn th => drule_all (cj 7 th)) >>
     strip_tac >> rename1 `c = EL (EL i inds) cxs` >>
     qpat_x_assum `!q. q < LENGTH cxs ==> _` (qspec_then `EL i inds` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`c = EL (EL i inds) cxs`,`c.inst_id = SND (EL i p)`,
        `c.inst_opcode = INVOKE`,`i < LENGTH p`,
        `FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) = SOME _`,
        `FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME ms`,
        `FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME ess`,
        `FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME ks`,
        `EL i inds < LENGTH ms`,`EL i inds < LENGTH ess`,`EL i inds < LENGTH ks`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[] >> simp[DROP_CONS_EL]) >>
  qabbrev_tac `(cm:bytes32 option list list) = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs)` >>
  qabbrev_tac `ce = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs)` >>
  qabbrev_tac `ck = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(p,d,(EL q xs).inst_id)] else []) (LENGTH xs)` >>
  qabbrev_tac `m0 = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `m1 = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_new (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `e0 = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `e1 = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es_new (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `k0 = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `k1 = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_new (DROP i p,f)))) (EL i orders))` >>
  `?lm rm le re lk rk.
    m0 (LENGTH p) = lm ++ rm /\ m1 (LENGTH p) = lm ++ FLAT cm ++ rm /\
    e0 (LENGTH p) = le ++ re /\ e1 (LENGTH p) = le ++ FLAT ce ++ re /\
    k0 (LENGTH p) = lk ++ rk /\ k1 (LENGTH p) = lk ++ FLAT ck ++ rk /\
    LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
    LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk` by
    (irule dft_packet_existing_path_triple_insertion >>
     ntac 2 (conj_tac
     >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         simp[Abbr `cm`,Abbr `ce`,Abbr `ck`,LENGTH_FLAT,MAP_GENLIST,combinTheory.o_DEF] >>
         AP_TERM_TAC >> irule GENLIST_CONG >>
         rpt strip_tac >> simp[] >> IF_CASES_TAC >> simp[])) >>
     qexistsl [`d`,`ds`,`es_tab`,`es_new`,`inds`,`ks_tab`,`ks_new`,
       `ms_tab`,`ms_new`,`orders`] >>
     simp[Abbr `m0`,Abbr `m1`,Abbr `e0`,Abbr `e1`,Abbr `k0`,Abbr `k1`,
       Abbr `cm`,Abbr `ce`,Abbr `ck`] >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         qpat_assum `!i. i < LENGTH p ==> ?mr er kr. _` drule >>
         disch_then (qx_choose_then `mr` (qx_choose_then `er` (qx_choose_then `kr` strip_assume_tac))) >>
         qpat_assum `!i. i <= LENGTH p ==> AM (DROP i p) = _ /\ _` (qspec_then `i` mp_tac) >>
         (impl_tac >- (qpat_assum `i < LENGTH p` mp_tac >>
           rpt (pop_assum kall_tac) >> decide_tac)) >> strip_tac >>
         qexistsl [`mr`,`er`,`kr`] >>
         qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP ms_tab _ = SOME rows ==> _`
           (fn th => drule_all (cj 1 th)) >> strip_tac >>
         qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP es_tab _ = SOME rows ==> _`
           (fn th => drule_all (cj 1 th)) >> strip_tac >>
         qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP ks_tab _ = SOME rows ==> _`
           (fn th => drule_all (cj 1 th)) >> strip_tac >>
         map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
           [`ms_new = EL (LENGTH p) mt`,`es_new = EL (LENGTH p) et`,
            `ks_new = EL (LENGTH p) kt`] >>
         asm_rewrite_tac[]) >>
     asm "block_records" drule >> simp_tac std_ss [] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  rename1 `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,NONE,0,OK s,F,NONE)` >>
  qabbrev_tac `new_blocks = blocks |+ ((p,d),
    (bb,bt,ps,xs,ys,schedule,in_state,h0,
     if SUC k < LENGTH ps then NONE else SOME (s1,SUC j),0,OK s1,F,NONE))` >>
  qabbrev_tac `ms1 = if SUC k < LENGTH ps then ms_tab else ms_new` >>
  qabbrev_tac `es1 = if SUC k < LENGTH ps then es_tab else es_new` >>
  qabbrev_tac `ks1 = if SUC k < LENGTH ps then ks_tab else ks_new` >>
  qabbrev_tac `AM1 = \a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms1 (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))` >>
  qabbrev_tac `AE1 = \a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es1 (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))` >>
  qabbrev_tac `AK1 = \a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks1 (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))` >>
  `~(SUC k < LENGTH ps) ==> SUC k = LENGTH ps` by
    (qpat_assum `k < LENGTH ps` mp_tac >> rpt (pop_assum kall_tac) >> decide_tac) >>
  qexistsl [`new_blocks`,`ms1`,`es1`,`ks1`,`AM1`,`AE1`,`AK1`,`inds`,`orders`] >>
  conj_tac >- simp[Abbr `new_blocks`] >>
  ntac 4 (conj_tac >- (first_assum ACCEPT_TAC)) >>
  conj_tac
  >- (Cases_on `SUC k < LENGTH ps`
      >- (disj1_tac >> qpat_assum `SUC k < LENGTH ps` (fn th =>
            simp[NoAsms,th,Abbr `ms1`,Abbr `es1`,Abbr `ks1`])) >>
      disj2_tac >> conj_tac
      >- (qpat_assum `~(SUC k < LENGTH ps) ==> SUC k = LENGTH ps` drule >>
          disch_then ACCEPT_TAC) >>
      qexistsl [`mt`,`et`,`kt`] >>
      map_every (fn pat => qpat_assum pat
        (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
        [`Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`] >>
      map_every (fn pat => qpat_assum pat
        (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]))
        [`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
      asm_rewrite_tac[] >> (simp[])) >>
  conj_tac >- simp[NoAsms,Abbr `AM1`] >>
  conj_tac >- simp[NoAsms,Abbr `AE1`] >>
  conj_tac >- simp[NoAsms,Abbr `AK1`] >>
  ntac 3 (conj_tac >- (first_assum ACCEPT_TAC)) >>
  `s1.vs_gas_readings = s.vs_gas_readings` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`s1 = u with vs_inst_idx := SUC k`, `is_pseudo inst.inst_opcode`,
       `step_inst g C8 inst s = OK u`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
       (Cases_on `inst.inst_opcode` >> gvs[is_pseudo_def]) >>
     drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >> simp[]) >>
  conj_tac >- (map_every (fn pat => qpat_assum pat (fn th => rewrite_tac [th]))
    [`s1.vs_gas_readings = s.vs_gas_readings`,
     `root_entry.vs_gas_readings = MAP SND obs ++ s.vs_gas_readings`]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT (FLAT ck) /\ (!v. MEM v (FLAT ck) ==> ~MEM v (AK [])) /\
   (!cid. ALOOKUP obs (p,d,cid) = NONE)` by suspend "fresh_aggregate_keys" >>
  `ALL_DISTINCT (AK1 []) /\ LENGTH (AM1 []) = LENGTH (AE1 []) /\
   LENGTH (AM1 []) = LENGTH (AK1 []) /\
   PERM (MAP (\(key,slot). (key,THE slot))
     (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK1 [],AM1 [])))) obs /\
   MAP THE (FILTER IS_SOME (AM1 [])) = MAP THE (FILTER IS_SOME (AM []))` by
    suspend "conservation" >>
  ntac 4 (conj_tac >- (first_assum ACCEPT_TAC)) >>
  conj_tac >- (map_every (fn pat => qpat_assum pat (fn th => rewrite_tac [th]))
    [`s1.vs_gas_readings = s.vs_gas_readings`, `MAP THE (FILTER IS_SOME (AM1 [])) = _`]) >>
  suspend "remaining_clauses"
QED

Resume dft_packet_pseudo_next_clauses[conservation]:
  Cases_on `SUC k < LENGTH ps`
  >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`SUC k < LENGTH ps`,`Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,
        `Abbrev (ks1 = _)`,`Abbrev (AM1 = _)`,`Abbrev (AE1 = _)`,`Abbrev (AK1 = _)`,
        `ALL_DISTINCT (AK [])`,`LENGTH (AM []) = LENGTH (AE [])`,
        `LENGTH (AM []) = LENGTH (AK [])`,`PERM _ obs`] >>
      map_every (fn n => asm n mp_tac) ["AMeq","AEeq","AKeq"] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      gvs[Abbr `AM1`,Abbr `AE1`,Abbr `AK1`,Abbr `ms1`,Abbr `es1`,Abbr `ks1`]) >>
  `EL (LENGTH p) orders = order'` by
    (qpat_assum `Abbrev (orders = _)` mp_tac >>
     qpat_assum `FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order',NONE,NONE)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[Abbr `orders`,DROP_LENGTH_NIL]) >>
  `AM [] = m0 (LENGTH p) /\ AE [] = e0 (LENGTH p) /\ AK [] = k0 (LENGTH p)` by
    (qpat_assum `!i. i <= LENGTH p ==> AM (DROP i p) = _ /\ _`
      (qspec_then `LENGTH p` mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (m0 = _)`,`Abbrev (e0 = _)`,`Abbrev (k0 = _)`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[DROP_LENGTH_NIL,Abbr `m0`,Abbr `e0`,Abbr `k0`]) >>
  `AM1 [] = m1 (LENGTH p) /\ AE1 [] = e1 (LENGTH p) /\ AK1 [] = k1 (LENGTH p)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`~(SUC k < LENGTH ps)`,`Abbrev (m1 = _)`,`Abbrev (e1 = _)`,`Abbrev (k1 = _)`,
        `Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`,
        `Abbrev (AM1 = _)`,`Abbrev (AE1 = _)`,`Abbrev (AK1 = _)`,
        `FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order',NONE,NONE)`,
        `EL (LENGTH p) orders = order'`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[DROP_LENGTH_NIL,Abbr `m1`,Abbr `e1`,Abbr `k1`,
          Abbr `AM1`,Abbr `AE1`,Abbr `AK1`,Abbr `ms1`,Abbr `es1`,Abbr `ks1`]) >>
  `LENGTH (FLAT cm) = LENGTH (FLAT ce) /\ LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
   EVERY (\x. x = NONE) (FLAT cm)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
     rpt (pop_assum kall_tac) >> ntac 3 disch_tac >>
     let val lens = simp[Abbr `cm`,Abbr `ce`,Abbr `ck`,LENGTH_FLAT,MAP_GENLIST,combinTheory.o_DEF] >>
                      AP_TERM_TAC >> irule GENLIST_CONG >>
                      rpt strip_tac >> simp[] >> IF_CASES_TAC >> simp[]
     in conj_tac >- lens >> conj_tac >- lens end >>
     simp[Abbr `cm`,EVERY_FLAT,EVERY_GENLIST] >>
     rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`AM [] = m0 (LENGTH p)`,`AE [] = e0 (LENGTH p)`,`AK [] = k0 (LENGTH p)`,
     `AM1 [] = m1 (LENGTH p)`,`AE1 [] = e1 (LENGTH p)`,`AK1 [] = k1 (LENGTH p)`,
     `m0 (LENGTH p) = _`,`m1 (LENGTH p) = _`,`e0 (LENGTH p) = _`,
     `e1 (LENGTH p) = _`,`k0 (LENGTH p) = _`,`k1 (LENGTH p) = _`,
     `LENGTH lm = LENGTH le`,`LENGTH lm = LENGTH lk`,
     `LENGTH rm = LENGTH re`,`LENGTH rm = LENGTH rk`,
     `LENGTH (FLAT cm) = LENGTH (FLAT ce)`,`LENGTH (FLAT cm) = LENGTH (FLAT ck)`,
     `EVERY (\x. x = NONE) (FLAT cm)`,`ALL_DISTINCT (FLAT ck)`,
     `!v. MEM v (FLAT ck) ==> ~MEM v (AK [])`,
     `ALL_DISTINCT (AK [])`,`PERM _ obs`] >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  `LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
   LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk /\
   LENGTH (FLAT cm) = LENGTH (FLAT ce) /\ LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
   EVERY (\x. x = NONE) (FLAT cm)` suffices_by
    (disch_then (mp_tac o MATCH_MP dft_packet_call_insertion_conservation) >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[fresh_aggregate_keys]:
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)`,
        `bb.bb_instructions = ps ++ xs`] >>
     rpt (pop_assum kall_tac) >> simp[MAP_APPEND,ALL_DISTINCT_APPEND]) >>
  `!a sf tf inc entry order res rest f.
     FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\ MEM f order ==>
     (a,f) IN FDOM blocks` by
    (asm "activations" mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!a f bb bt ps xs ys rho hin h0 body count front closed brest.
    FLOOKUP blocks (a,f) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
    (case body of
      NONE => FLOOKUP ks_tab (a,f) = SOME []
    | SOME be => ?ks.
        FLOOKUP ks_tab (a,f) = SOME ks /\ LENGTH ks = LENGTH xs /\
        (!q. q < LENGTH xs ==>
          ((EL q xs).inst_opcode = GAS ==> EL q ks = [(a,f,(EL q xs).inst_id)]) /\
          ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==> EL q ks = []) /\
          ((EL q xs).inst_opcode = INVOKE ==>
            (case FLOOKUP calls (a,f,(EL q xs).inst_id) of
              NONE => EL q ks = []
            | SOME call => ?csf ctf cinc centry corder cres crest.
                FLOOKUP acts ((f,(EL q xs).inst_id)::a) =
                  SOME (csf,ctf,cinc,centry,corder,cres,crest) /\
                EL q ks = FLAT (MAP (\g. FLAT
                  (THE (FLOOKUP ks_tab (((f,(EL q xs).inst_id)::a),g)))) corder)))))` by
    suspend "old_key_rows" >>
  `ck = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(p,d,(EL q xs).inst_id)] else []) (LENGTH xs)` by
    simp[NoAsms,Abbr `ck`] >>
  `LENGTH (AK []) = LENGTH (AM [])` by
    (qpat_assum `LENGTH (AM []) = LENGTH (AK [])` (ACCEPT_TAC o SYM)) >>
  asm "AKeq" assume_tac >>
  drule_all dft_packet_pseudo_key_freshness >>
  strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  `!cid. ~MEM (p,d,cid) (AK [])` by
    (qpat_assum `!a sf tf inc entry order res rest cid. _ ==> ~MEM _ _` drule >> simp[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`ck = GENLIST _ _`,`!cid. ~MEM (p,d,cid) (AK [])`] >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  simp[MEM_FLAT,MEM_GENLIST] >> rpt strip_tac >>
  rename1 `l = if (EL q xs).inst_opcode = GAS then _ else []` >>
  Cases_on `(EL q xs).inst_opcode = GAS` >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[old_key_rows]:
  map_every qx_gen_tac [`a0`,`f0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,
    `hin0`,`hi0`,`body0`,`count0`,`front0`,`closed0`,`brest0`] >> disch_tac >>
  qpat_assum `FLOOKUP blocks (a0,f0) = SOME _`
    (fn th => asm "block_records" (mp_tac o C MATCH_MP th)) >>
  namedCases_on `body0` ["", "beh"]
  >- (simp_tac pure_ss [optionTheory.option_case_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  PairCases_on `beh` >> simp_tac pure_ss [optionTheory.option_case_def] >> strip_tac >>
  `?ms ess ks. FLOOKUP ms_tab (a0,f0) = SOME ms /\
     FLOOKUP es_tab (a0,f0) = SOME ess /\ FLOOKUP ks_tab (a0,f0) = SOME ks` by
    (qpat_assum `!a e. (a,e) IN FDOM blocks ==> _` irule >>
     qpat_assum `FLOOKUP blocks (a0,f0) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[flookup_thm]) >>
  qexists_tac `ks` >>
  asm "rows" (fn th => drule_all (cj 1 th)) >> strip_tac >>
  asm "rows" (fn th => drule_all (cj 3 th)) >> strip_tac >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `LENGTH ks = LENGTH ms` (fn th => simp[NoAsms,th]) >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `q0` >> disch_tac >>
  asm "rows" (fn th => drule_all (cj 7 th)) >>
  disch_then (fn th => qpat_assum `q0 < LENGTH xs0`
    (fn hq => mp_tac (MATCH_MP (CONJUNCT1 th) hq))) >>
  strip_tac >>
  conj_tac >- (strip_tac >> simp[]) >>
  conj_tac >- (strip_tac >> simp[]) >> disch_tac >>
  qpat_x_assum `(EL q0 xs0).inst_opcode = INVOKE ==> _` drule >>
  namedCases_on `FLOOKUP calls (a0,f0,(EL q0 xs0).inst_id)` ["", "call0"]
  >- simp[] >>
  PairCases_on `call0` >> simp_tac pure_ss [optionTheory.option_case_def] >> strip_tac >>
  qpat_assum `FLOOKUP calls (a0,f0,(EL q0 xs0).inst_id) = SOME _`
    (fn th => asm "call_records" (mp_tac o C MATCH_MP th)) >> strip_tac >>
  asm "AKeq" (fn th => simp[th]) >> metis_tac[]
QED

Resume dft_packet_pseudo_next_clauses[remaining_clauses]:
  `(p,d) IN FDOM blocks` by
    (qpat_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[flookup_thm]) >>
  `FDOM new_blocks = FDOM blocks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`Abbrev (new_blocks = _)`, `(p,d) IN FDOM blocks`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[Abbr `new_blocks`, EXTENSION] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  let fun dom out new old =
    conj_tac >-
      (qpat_assum out (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [new,old,`(p,d) IN FDOM blocks`,`FDOM new_blocks = FDOM blocks`] >>
       rpt (pop_assum kall_tac) >> rpt strip_tac >>
       Cases_on `SUC k < LENGTH ps`
       >- simp[] >>
       simp[EXTENSION] >> metis_tac[])
  in
    dom `Abbrev (ms1 = _)` `FDOM ms_new = _` `FDOM blocks = FDOM ms_tab` >>
    dom `Abbrev (es1 = _)` `FDOM es_new = _` `FDOM blocks = FDOM es_tab` >>
    dom `Abbrev (ks1 = _)` `FDOM ks_new = _` `FDOM blocks = FDOM ks_tab`
  end >>
  suspend "after_domains"
QED

Resume dft_packet_pseudo_next_clauses[after_domains]:
  `!a e. (a,e) <> (p,d) ==> FLOOKUP new_blocks (a,e) = FLOOKUP blocks (a,e)` by
    (qpat_assum `Abbrev (new_blocks = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[Abbr `new_blocks`, FLOOKUP_UPDATE] >> metis_tac[]) >>
  pop_assum (mk_asm "off_block") >>
  `!a e. (?pb pt pps pxs pys prho pin ph pbe pc pr pu.
      FLOOKUP blocks (a,e) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,pr,T,SOME pu)) ==>
    FLOOKUP new_blocks (a,e) = FLOOKUP blocks (a,e)` by
    (rpt gen_tac >> strip_tac >> asm "off_block" irule >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,_,_,_,T,SOME _)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,NONE,0,OK s,F,NONE)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  pop_assum (mk_asm "closed_block_frame") >>
  `!a e. (?pb pt pps pxs pys prho pin ph be hbe pc pr c rest.
      FLOOKUP blocks (a,e) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,SOME (be,hbe),pc,pr,c,rest)) ==>
    FLOOKUP new_blocks (a,e) = FLOOKUP blocks (a,e)` by
    (rpt gen_tac >> strip_tac >> asm "off_block" irule >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,NONE,0,OK s,F,NONE)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  pop_assum (mk_asm "body_block_frame") >>
  `FLOOKUP new_blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,
      if SUC k < LENGTH ps then NONE else SOME (s1,SUC j),0,OK s1,F,NONE)` by
    (qpat_assum `Abbrev (new_blocks = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> simp[Abbr `new_blocks`,FLOOKUP_UPDATE]) >>
  pop_assum (mk_asm "current_block_next") >>
  conj_tac >- suspend "block_records_next" >>
  conj_tac >- suspend "cursor_block_next" >>
  conj_tac >- suspend "cursor_inst_next" >>
  conj_tac >- suspend "cursor_phase_next" >>
  conj_tac >- suspend "call_records_next" >>
  conj_tac >- suspend "parents_next" >>
  suspend "semantic_clauses"
QED

Resume dft_packet_pseudo_next_clauses[cursor_block_next]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`s1 = u with vs_inst_idx := SUC k`, `lookup_block s.vs_current_bb fn.fn_blocks = SOME bt`,
     `step_inst g C8 inst s = OK u`, `is_pseudo inst.inst_opcode`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  `~is_terminator inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
   ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >>
     gvs[is_pseudo_def,is_terminator_def,is_alloca_op_def,is_ext_call_op_def]) >>
  drule_all passSharedFieldTheory.step_inst_preserves_all >> strip_tac >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[cursor_inst_next]:
  first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[cursor_phase_next]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`SUC k <= LENGTH ps`, `l <= k`, `s1.vs_inst_idx = SUC k`,
     `phi_prefix_length bt.bb_instructions = l`,
     `eval_phis in_state bt.bb_instructions = OK sp`,
     `FOLDR (dft_exec_cons (N-d) C8) OK (DROP l (TAKE (SUC k) ps)) _ = OK s1`,
     `SUC k = LENGTH ps ==> _ /\ _`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `SUC k < LENGTH ps`
  >- simp[] >>
  `SUC k = LENGTH ps` by decide_tac >>
  qpat_assum `SUC k = LENGTH ps ==> _` drule >>
  strip_tac >> gvs[EL, LENGTH_NIL] >> Cases_on `ys` >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[parents_next]:
  qx_gen_tac `i` >> strip_tac >>
  asm "parents" (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  asm "body_block_frame" mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  rename1 `FLOOKUP blocks (a0,e0) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)` >>
  `FLOOKUP new_blocks (a0,e0) = FLOOKUP blocks (a0,e0)` by
    (first_x_assum irule >> rpt (irule_at Any (ASSUME ``T``)) >> metis_tac[]) >>
  metis_tac[]
QED

Resume dft_packet_pseudo_next_clauses[call_records_next]:
  rpt gen_tac >> strip_tac >> asm "call_records" drule >>
  asm "body_block_frame" mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  let val ws = [`sf0`,`tf0`,`inc0`,`entry0`,`order0`,`res0`,`nrest0`,
      `bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,`h00`,
      `be0`,`hbe0`,`count0`,`front0`,`closed0`,`rest0`,
      `csf0`,`ctf0`,`corder0`,`cres0`,`crest0`,`c0`,`nm0`,`ops0`,`args0`]
  in
    disch_then (List.foldr (fn (v,t) => qx_choose_then v t) strip_assume_tac ws) >>
    `FLOOKUP new_blocks (a,e) = FLOOKUP blocks (a,e)` by
      (first_x_assum irule >> metis_tac[]) >>
    qexistsl ws
  end >>
  simp[] >> Cases_on `ret` >> gvs[] >> PairCases_on `x` >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[block_records_next]:
  `!a e inc in0 ent0.
      (if e = SUC inc then in0 = ent0 else
         ?pb pt pps pxs pys prho pin ph pbe pc pu.
           FLOOKUP blocks (a,e-1) =
             SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK in0,T,SOME pu) /\ ~in0.vs_halted) ==>
      (if e = SUC inc then in0 = ent0 else
         ?pb pt pps pxs pys prho pin ph pbe pc pu.
           FLOOKUP new_blocks (a,e-1) =
             SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK in0,T,SOME pu) /\ ~in0.vs_halted)` by
    (asm "closed_block_frame" mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
     rpt gen_tac >> Cases_on `e = SUC inc` >- simp[] >>
     simp[] >> strip_tac >> first_x_assum (qspecl_then [`a`,`e-1`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> metis_tac[]) >>
  pop_assum (mk_asm "predecessor_frame") >>
  map_every qx_gen_tac [`a0`,`depth0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,
    `h00`,`bentry0`,`count0`,`front0`,`closed0`,`rest0`] >> strip_tac >>
  Cases_on `(a0,depth0) = (p,d)` >- suspend "current_block_record" >>
  `FLOOKUP new_blocks (a0,depth0) = FLOOKUP blocks (a0,depth0)` by
    (asm "off_block" irule >> first_assum ACCEPT_TAC) >>
  `FLOOKUP blocks (a0,depth0) = SOME (bb0,bt0,ps0,xs0,ys0,rho0,in0,h00,bentry0,count0,front0,closed0,rest0)` by
    (qpat_assum `FLOOKUP new_blocks (a0,depth0) = FLOOKUP blocks (a0,depth0)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  asm "block_records" (qspecl_then [`a0`,`depth0`] drule) >>
  asm "predecessor_frame" (qspecl_then [`a0`,`depth0`] mp_tac) >>
  qpat_assum `(a0,depth0) <> (p,d)` mp_tac >>
  rpt (pop_assum kall_tac) >> ntac 2 strip_tac >>
  let val ws = [`sf0`,`tf0`,`inc0`,`entry0`,`order0`,`res0`,`nrest0`,`sp0`] in
    disch_then (List.foldr (fn (v,t) => qx_choose_then v t) strip_assume_tac ws) >>
    qexistsl ws
  end >>
  simp[] >>
  `h00 <= SUC j` by simp[] >> simp[] >>
  conj_tac
  >- (qpat_assum `if depth0 = SUC inc0 then _ else _` mp_tac >>
      qpat_assum `!inc in0 ent0. _` (qspecl_then [`inc0`,`in0`,`entry0`] mp_tac) >>
      rpt (pop_assum kall_tac) >> Cases_on `depth0 = SUC inc0` >> simp[]) >>
  namedCases_on `bentry0` ["","be0"] >- gvs[] >> PairCases_on `be0` >> gs[] >>
  metis_tac[]
QED

Resume dft_packet_pseudo_next_clauses[current_block_record]:
  `a0 = p /\ depth0 = d` by
    (qpat_assum `(a0,depth0) = (p,d)` mp_tac >> simp[]) >>
  qpat_x_assum `a0 = p` SUBST_ALL_TAC >> qpat_x_assum `depth0 = d` SUBST_ALL_TAC >>
  asm "current_block_next" (fn th =>
    qpat_x_assum `FLOOKUP new_blocks (p,d) = SOME (bb0,bt0,_,_,_,_,_,_,_,_,_,_,_)`
      (mp_tac o REWRITE_RULE [th])) >>
  simp_tac pure_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  qexistsl [`sf`,`fn`,`inc`,`entry`,`order`,`NONE`,`NONE`,`sp`] >>
  `h0 <= SUC j` by simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `if d = SUC inc then _ else _` mp_tac >>
      asm "predecessor_frame" (qspecl_then [`p`,`d`,`inc`,`in_state`,`entry`] mp_tac) >>
      rpt (pop_assum kall_tac) >> Cases_on `d = SUC inc` >> simp[]) >>
  Cases_on `SUC k < LENGTH ps`
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`,
         `(case (NONE:(venom_state # num) option) of NONE => _ | SOME _ => _)`,
         `SUC k < LENGTH ps`,`LAST order = d`] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      simp[Abbr `ms1`,Abbr `es1`,Abbr `ks1`] >>
      qpat_assum `(case (NONE:(venom_state # num) option) of NONE => _ | SOME _ => _)`
        (strip_assume_tac o REWRITE_RULE [optionTheory.option_case_def]) >>
      gvs[]) >>
  `SUC k = LENGTH ps` by (qpat_assum `~(SUC k < LENGTH ps) ==> _` drule >> simp[]) >>
  qpat_assum `SUC k = LENGTH ps ==> dft_remaining_inv sf bb xs s1` drule >> strip_tac >>
  qpat_assum `SUC k = LENGTH ps ==> ys <> [] /\ _` drule >> strip_tac >>
  `s1.vs_current_bb = bb.bb_label` by fs[dft_remaining_inv_def] >>
  `s1.vs_inst_idx = LENGTH ps` by simp[] >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`SUC k = LENGTH ps`,`s1.vs_current_bb = bb.bb_label`,`s1.vs_inst_idx = LENGTH ps`,
     `dft_remaining_inv sf bb xs s1`,`i1 = HD ys`,`~(SUC k < LENGTH ps)`,
     `EL (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) = _`,
     `FOLDR (dft_exec_cons (N-d) C8) OK (DROP l (TAKE (SUC k) ps)) _ = OK s1`,
     `phi_prefix_length bt.bb_instructions = l`,`bt.bb_instructions = ps ++ ys`,
     `LAST order = d`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[semantic_clauses]:
  `!a e cid q h b done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child_entry,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of
        NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
      | SOME triple => MEM q (TAKE pos rho))` by suspend "history_call_shape" >>
  `!i. i < LENGTH p ==>
    ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,call_h,b0,done_at_call,child_entry,NONE) /\
      dft_fn_rel sf tf /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
      b0.vs_inst_idx = LENGTH ps + pos /\
      get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs)` by suspend "history_parent_shape" >>
  `!a e cid q h b done ent ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,ent,ret) ==>
    (?row. FLOOKUP ms_tab (a,e) = SOME row /\ q < LENGTH row /\
      EL q row = AM ((e,cid)::a) /\
      cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    (?row. FLOOKUP es_tab (a,e) = SOME row /\ q < LENGTH row /\
      EL q row = AE ((e,cid)::a) /\
      cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id) /\
    (?row. FLOOKUP ks_tab (a,e) = SOME row /\ q < LENGTH row /\
      EL q row = AK ((e,cid)::a) /\
      cid = (EL q (FST (SND (SND (SND (THE (FLOOKUP blocks (a,e)))))))).inst_id)` by
    suspend "history_call_cells" >>
  pop_assum (mk_asm "history_call_cells") >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "history_mask_update"))
  `ms1 = ms_tab \/
     ((!a e. (a,e) <> (p,d) /\
       (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
       FLOOKUP ms1 (a,e) = FLOOKUP ms_tab (a,e)) /\
      (!i row. i < LENGTH p /\
        FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
        FLOOKUP ms1 (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP ms1 (DROP i p,f))))
            (EL i orders))) (EL i inds) row)))`
  >- suspend "history_mask_update") >>
  let
    fun update abbrev out_eq final off_path row_update =
      Cases_on `SUC k < LENGTH ps` >- (disj1_tac >> simp[Abbr abbrev]) >>
      disj2_tac >> (out_eq by simp[Abbr abbrev]) >>
      qpat_assum out_eq SUBST1_TAC >> conj_tac
      >- (map_every qx_gen_tac [`a0`,`e0_num`] >> strip_tac >>
          qpat_assum final SUBST1_TAC >> qpat_assum off_path irule >> simp[]) >>
      map_every qx_gen_tac [`i`,`row`] >> strip_tac >>
      qpat_assum row_update (qspecl_then [`i`,`row`] mp_tac) >>
      (impl_tac >- simp[]) >> disch_then (ACCEPT_TAC o cj 1)
  in
    (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "history_site_update"))
    `es1 = es_tab \/
       ((!a e. (a,e) <> (p,d) /\
         (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
         FLOOKUP es1 (a,e) = FLOOKUP es_tab (a,e)) /\
        (!i row. i < LENGTH p /\
          FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
          FLOOKUP es1 (DROP (SUC i) p,FST (EL i p)) =
            SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP es1 (DROP i p,f))))
              (EL i orders))) (EL i inds) row)))`
    >- update `es1` `es1 = es_new` `es_new = EL (LENGTH p) et`
         `!i a e. i <= LENGTH p /\ _ ==> FLOOKUP (EL i et) (a,e) = _`
         `!i rows. i < LENGTH p /\ FLOOKUP es_tab _ = SOME rows ==> _`) >>
    (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "history_key_update"))
    `ks1 = ks_tab \/
       ((!a e. (a,e) <> (p,d) /\
         (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
         FLOOKUP ks1 (a,e) = FLOOKUP ks_tab (a,e)) /\
        (!i row. i < LENGTH p /\
          FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME row ==>
          FLOOKUP ks1 (DROP (SUC i) p,FST (EL i p)) =
            SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks1 (DROP i p,f))))
              (EL i orders))) (EL i inds) row)))`
    >- update `ks1` `ks1 = ks_new` `ks_new = EL (LENGTH p) kt`
         `!i a e. i <= LENGTH p /\ _ ==> FLOOKUP (EL i kt) (a,e) = _`
         `!i rows. i < LENGTH p /\ FLOOKUP ks_tab _ = SOME rows ==> _`)
  end >>
  asm "activations" (fn th => assume_tac (cj 9 th)) >>
  let
    fun frame eqname update i abbrev result =
      asm eqname assume_tac >>
      asm "history_call_cells" (fn th => assume_tac (cj i th)) >>
      qpat_assum abbrev (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      asm update (mp_then (Pos (el 11)) (drule_all_then (mk_asm result))
        dft_packet_pseudo_history_frame)
  in
    frame "AMeq" "history_mask_update" 1 `Abbrev (AM1 = _)` "mask_history" >>
    frame "AEeq" "history_site_update" 2 `Abbrev (AE1 = _)` "site_history" >>
    frame "AKeq" "history_key_update" 3 `Abbrev (AK1 = _)` "key_history"
  end >>
  `!i. i <= LENGTH p ==>
     LENGTH (AM1 (DROP i p)) = LENGTH (AE1 (DROP i p)) /\
     LENGTH (AM1 (DROP i p)) = LENGTH (AK1 (DROP i p)) /\
     (!f. MEM f (EL i orders) ==>
       LIST_REL (\x y. LENGTH x = LENGTH y)
         (THE (FLOOKUP ms1 (DROP i p,f))) (THE (FLOOKUP es1 (DROP i p,f))) /\
       LIST_REL (\x y. LENGTH x = LENGTH y)
         (THE (FLOOKUP ms1 (DROP i p,f))) (THE (FLOOKUP ks1 (DROP i p,f))))` by
    suspend "path_alignment" >>
  `!i f. i <= LENGTH p /\ MEM f (EL i orders) /\
      ALL_DISTINCT (AK1 (DROP i p)) ==>
      ALL_DISTINCT (FLAT (THE (FLOOKUP ks1 (DROP i p,f))))` by
    suspend "path_row_distinct" >>
  `!i. i <= LENGTH p ==> ALL_DISTINCT (AK1 (DROP i p))` by
    suspend "path_aggregate_distinct" >>
  conj_tac >- suspend "row_replay_next" >>
  conj_tac >- suspend "caller_Q_next" >>
  conj_tac >- suspend "closed_row_next" >>
  conj_tac >- suspend "closed_activation_next" >>
  conj_tac >- suspend "completed_call_next" >>
  conj_tac >- suspend "current_observation_next" >>
  suspend "rooted_cuts_next"
QED

Resume dft_packet_pseudo_next_clauses[completed_call_next]:
  map_every qx_gen_tac [`a0`,`depth0`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,
    `h00`,`be0`,`hbe0`,`count0`,`front0`,`closed0`,`rest0`] >> strip_tac >>
  Cases_on `(a0,depth0) = (p,d)`
  >- (qpat_assum `(a0,depth0) = (p,d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      qpat_x_assum `a0 = p` SUBST_ALL_TAC >> qpat_x_assum `depth0 = d` SUBST_ALL_TAC >>
      asm "current_block_next" (fn th =>
        qpat_assum `FLOOKUP new_blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
          (mp_tac o REWRITE_RULE [th])) >>
      rpt (pop_assum kall_tac) >> IF_CASES_TAC >> simp[]) >>
  `FLOOKUP new_blocks (a0,depth0) = FLOOKUP blocks (a0,depth0)` by
    (asm "off_block" irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `FLOOKUP new_blocks (a0,depth0) = FLOOKUP blocks (a0,depth0)` (fn th =>
    qpat_assum `FLOOKUP new_blocks (a0,depth0) = SOME _`
      (assume_tac o REWRITE_RULE [th])) >>
  asm "old_completed_calls" (fn th =>
    qpat_assum `FLOOKUP blocks (a0,depth0) = SOME _` (ACCEPT_TAC o MATCH_MP th))
QED

Resume dft_packet_pseudo_next_clauses[current_observation_next]:
  map_every qx_gen_tac [`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,`h00`,
    `be0`,`hbe0`,`count0`,`sf0`,`inc0`,`ent0`,`ord0`] >> strip_tac >>
  qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (fn th =>
    qpat_x_assum `FLOOKUP acts p = SOME (sf0,fn,inc0,ent0,ord0,NONE,NONE)`
      (mp_tac o REWRITE_RULE [th])) >>
  simp_tac pure_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  asm "current_block_next" (fn th =>
    qpat_x_assum `FLOOKUP new_blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
      (mp_tac o REWRITE_RULE [th])) >>
  Cases_on `SUC k < LENGTH ps`
  >- (qpat_assum `SUC k < LENGTH ps` mp_tac >> rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_assum `~(SUC k < LENGTH ps)` (fn th => simp_tac std_ss
    [th,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  `SUC k = LENGTH ps` by (qpat_assum `~(SUC k < LENGTH ps) ==> _` drule >> simp[]) >>
  qpat_assum `SUC k = LENGTH ps ==> ys <> [] /\ _` drule >> strip_tac >>
  `inv_memory_observation (HD ys).inst_opcode` by
    (qpat_assum `i1 = HD ys` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `EL 0 schedule < LENGTH xs /\ EL (EL 0 schedule) xs = HD ys /\
   EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL 0 schedule) xs) /\
   EVERY (\i. i.inst_opcode <> INVOKE) (TAKE (EL 0 schedule) xs)` by
    ((MATCH_MP_TAC dft_packet_first_body_schedule >>
     qexistsl_tac [`sf`,`fn`,`bb`,`bt`,`ps`,`schedule`] >>
     rpt (conj_tac >- pure_asm_rewrite_tac []) >> pure_asm_rewrite_tac [] >> (simp[dft_packet_first_body_schedule]))) >>
  qpat_assum `i1 = HD ys` SUBST1_TAC >>
  simp[TAKE_0] >>
  qx_gen_tac `r` >> rpt strip_tac >>
  qpat_assum `r < HD schedule` mp_tac >>
  qpat_assum `EL 0 schedule < LENGTH xs` mp_tac >>
  qpat_assum `(EL r xs).inst_opcode = INVOKE` mp_tac >>
  qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE) (TAKE _ xs)`
    (qspec_then `r` mp_tac o REWRITE_RULE [EVERY_EL]) >>
  rpt (pop_assum kall_tac) >>
  rewrite_tac [listTheory.EL, LENGTH_TAKE_EQ] >>
  Cases_on `HD schedule <= LENGTH xs` >> simp[EL_TAKE] >> metis_tac[]
QED

Resume dft_packet_pseudo_next_clauses[history_call_shape]:
  rpt gen_tac >> strip_tac >> asm "call_records" drule >>
  rpt (pop_assum kall_tac) >>
  let val ws = [`sf0`,`tf0`,`inc0`,`entry0`,`order0`,`res0`,`rest0`,
      `bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`hin0`,`h00`,`be0`,`hbe0`,
      `pos0`,`front0`,`closed0`,`brest0`,`csf0`,`ctf0`,`corder0`,`cres0`,
      `crest0`,`c0`,`nm0`,`ops0`,`args0`] in
    disch_then (List.foldr (fn (v,t) => qx_choose_then v t) strip_assume_tac ws)
  end >>
  qexistsl [`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`hin0`,`h00`,`be0`,`hbe0`,
    `pos0`,`front0`,`closed0`,`brest0`] >>
  Cases_on `ret` >- gvs[] >> PairCases_on `x` >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[history_parent_shape]:
  qx_gen_tac `i` >> strip_tac >>
  asm "parents" (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_assum `(e,cid) = EL i p` (fn th =>
    assume_tac (REWRITE_RULE [pairTheory.FST,pairTheory.SND] (AP_TERM ``FST : num # num -> num`` th)) >>
    assume_tac (REWRITE_RULE [pairTheory.FST,pairTheory.SND] (AP_TERM ``SND : num # num -> num`` th))) >>
  qpat_assum `!i. i < LENGTH p ==> ?call_h b0 done child_entry. _` drule >>
  disch_then strip_assume_tac >>
  asm "call_records" (qspecl_then [`DROP (SUC i) p`,`FST (EL i p)`,`SND (EL i p)`] drule) >>
  strip_tac >> asm "block_records" (qspecl_then [`DROP (SUC i) p`,`FST (EL i p)`] drule) >>
  strip_tac >>
  asm "activations" (fn th => drule (cj 3 th)) >> strip_tac >>
  suspend "history_parent_witnesses"
QED

Resume dft_packet_pseudo_next_clauses[history_parent_witnesses]:
  rename1 `dft_fn_rel src dst` >>
  rename1 `FLOOKUP blocks (a,e) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,SOME(pbe,phbe),pc,OK b0,F,NONE)` >>
  qexistsl [`src`,`dst`,`pb`,`pt`,`pps`,`pxs`,`pys`,`prho`,`pin`,`ph`,`pbe`,`phbe`,
    `pc`,`b0`,`done_at_call`,`child_entry`,`h`] >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`a = DROP (SUC i) p`,`e = FST (EL i p)`,`cid = SND (EL i p)`,
     `FLOOKUP blocks (a,e) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,SOME(pbe,phbe),pc,OK b0,F,NONE)`,
     `FLOOKUP calls (a,e,cid) = SOME _`,
     `FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) = SOME _`,
     `FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) = SOME _`,
     `dft_fn_rel src dst`,
     `lookup_block _.bb_label src.fn_blocks = SOME _`,
     `lookup_block _.bb_label dst.fn_blocks = SOME _`,
     `bb''.bb_instructions = _`,`bt''.bb_instructions = _`,
     `EVERY (\x. is_pseudo x.inst_opcode) ps''`,
     `EVERY (\x. ~is_pseudo x.inst_opcode) xs''`,
     `LENGTH xs'' = LENGTH ys''`, `PERM rho'' (COUNT_LIST (LENGTH xs''))`,
     `LIST_REL _ rho'' ys''`, `EL i inds < LENGTH xs''`,
     `c = EL (EL i inds) xs''`, `c.inst_opcode = INVOKE`,
     `b0.vs_inst_idx = LENGTH pps + pc`, `get_instruction pt b0.vs_inst_idx = SOME _`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[history_call_cells]:
  map_every qx_gen_tac [`ca`,`ce_num`,`cid0`,`q0`,`h0'`,`b0`,`done0`,`ent0`,`ret0`] >>
  disch_tac >> asm "call_records" drule >> strip_tac >>
  `?mr er kr. FLOOKUP ms_tab (ca,ce_num) = SOME mr /\
    FLOOKUP es_tab (ca,ce_num) = SOME er /\ FLOOKUP ks_tab (ca,ce_num) = SOME kr` by
    (qpat_assum `!a e. (a,e) IN FDOM blocks ==> ?ms ess ks. _` irule >>
     qpat_assum `FLOOKUP blocks (ca,ce_num) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[flookup_thm]) >>
  asm "rows" (fn th => drule_all (cj 1 th)) >> strip_tac >>
  asm "rows" (fn th => drule_all (cj 2 th)) >> strip_tac >>
  asm "rows" (fn th => drule_all (cj 3 th)) >> strip_tac >>
  asm "rows" (fn th => drule_all (cj 7 th)) >>
  rename1 `c = EL q0 call_xs` >>
  disch_then (fn th => qpat_assum `q0 < LENGTH call_xs`
    (fn hq => mp_tac (MATCH_MP (CONJUNCT1 th) hq))) >>
  strip_tac >>
  qpat_assum `(EL q0 call_xs).inst_opcode = INVOKE ==> _` mp_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`c = EL q0 call_xs`,`c.inst_id = cid0`,`c.inst_opcode = INVOKE`,
     `q0 < LENGTH call_xs`,`FLOOKUP calls (ca,ce_num,cid0) = SOME _`,
     `FLOOKUP blocks (ca,ce_num) = SOME _`,
     `FLOOKUP ms_tab (ca,ce_num) = SOME mr`,`FLOOKUP es_tab (ca,ce_num) = SOME er`,
     `FLOOKUP ks_tab (ca,ce_num) = SOME kr`,
     `LENGTH mr = LENGTH call_xs`,`LENGTH er = LENGTH mr`,`LENGTH kr = LENGTH mr`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]

QED

Resume dft_packet_pseudo_next_clauses[history_mask_update]:
  Cases_on `SUC k < LENGTH ps` >- (disj1_tac >> simp[Abbr `ms1`]) >>
  disj2_tac >>
  `ms1 = ms_new` by simp[Abbr `ms1`] >>
  qpat_assum `ms1 = ms_new` SUBST1_TAC >>
  conj_tac
  >- (map_every qx_gen_tac [`a0`,`e0_num`] >> strip_tac >>
      qpat_assum `ms_new = EL (LENGTH p) mt` SUBST1_TAC >>
      qpat_assum `!i a e. i <= LENGTH p /\ _ ==> FLOOKUP (EL i mt) (a,e) = _`
        irule >> simp[]) >>
  map_every qx_gen_tac [`i`,`row`] >> strip_tac >>
  qpat_assum `!i rows. i < LENGTH p /\ FLOOKUP ms_tab _ = SOME rows ==> _`
    (qspecl_then [`i`,`row`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (ACCEPT_TAC o cj 1)
QED

Resume dft_packet_pseudo_next_clauses[caller_Q_next]:
  map_every qx_gen_tac [`a0`,`e0_num`,`cid0`,`q0`,`hc`,`b0`,`done0`,`child0`,`ret0`,
    `bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,`h00`,`be0`,`hbe0`,
    `count0`,`front0`,`closed0`,`rest0`,`ms0`] >> strip_tac >>
  Cases_on `(a0,e0_num) = (p,d)`
  >- (qpat_assum `(a0,e0_num) = (p,d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      qpat_x_assum `a0 = p` SUBST_ALL_TAC >> qpat_x_assum `e0_num = d` SUBST_ALL_TAC >>
      asm "mask_history" (fn th => qspec_then `cid0` mp_tac (cj 7 th)) >>
      qpat_assum `FLOOKUP calls (p,d,cid0) = SOME _` (fn th => simp_tac std_ss [th])) >>
  asm "off_block" (drule_then (fn th =>
    qpat_assum `FLOOKUP new_blocks (a0,e0_num) = SOME _` (assume_tac o REWRITE_RULE [th]))) >>
  asm "mask_history" (fn th => drule_then (assume_tac o cj 1) (cj 3 th)) >>
  qpat_assum `!a e cid q h b done ent ret. _ ==> ?row. FLOOKUP ms_tab (a,e) = SOME row /\ _`
    (drule_then (qx_choose_then `old_ms` strip_assume_tac)) >>
  asm "old_caller_Q" (drule_then (drule_then drule)) >>
  qpat_assum `TAKE q0 (THE (FLOOKUP ms1 (a0,e0_num))) = _` mp_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP ms1 (a0,e0_num) = SOME ms0`,`FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`] >>
  rpt (pop_assum kall_tac) >> ntac 2 strip_tac >> simp[] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[closed_row_next]:
  map_every qx_gen_tac [`a0`,`e0_num`,`sf0`,`tf0`,`inc0`,`ent0`,`ord0`,`r0`,`nr0`,
    `bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,`h00`,`be0`,`hbe0`,
    `count0`,`result0`,`unused0`,`ms0`,`ess0`,`ks0`] >> strip_tac >>
  Cases_on `(a0,e0_num) = (p,d)`
  >- (qpat_assum `(a0,e0_num) = (p,d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      qpat_x_assum `a0 = p` SUBST_ALL_TAC >> qpat_x_assum `e0_num = d` SUBST_ALL_TAC >>
      asm "current_block_next" (fn th =>
        qpat_assum `FLOOKUP new_blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,_,T,_)`
          (mp_tac o REWRITE_RULE [th])) >>
      simp_tac std_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
  asm "off_block" (drule_then (fn th =>
    qpat_assum `FLOOKUP new_blocks (a0,e0_num) = SOME _` (assume_tac o REWRITE_RULE [th]))) >>
  map_every (fn (label,lookup) => asm label (fn th => drule_then
    (fn eq => qpat_assum lookup (assume_tac o REWRITE_RULE [eq])) (cj 4 th)))
    [("mask_history",`FLOOKUP ms1 (a0,e0_num) = SOME ms0`),
     ("site_history",`FLOOKUP es1 (a0,e0_num) = SOME ess0`),
     ("key_history", `FLOOKUP ks1 (a0,e0_num) = SOME ks0`)] >>
  asm "old_closed_row" (drule_all_then ACCEPT_TAC)
QED

Resume dft_packet_pseudo_next_clauses[closed_activation_next]:
  map_every qx_gen_tac [`a0`,`sf0`,`tf0`,`inc0`,`ent0`,`ord0`,`result0`,`unused0`] >> disch_tac >>
  map_every (fn label => asm label (fn th => drule_then (SUBST1_TAC o cj 2) (cj 5 th)))
    ["mask_history","site_history","key_history"] >>
  asm "old_closed_activation" (drule_then ACCEPT_TAC)
QED

Resume dft_packet_pseudo_next_clauses[row_replay_next]:
  map_every qx_gen_tac [`a0`,`e0_num`,`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,
    `h00`,`be0`,`hbe0`,`count0`,`front0`,`closed0`,`rest0`,`ms0`,`ess0`,`ks0`] >> strip_tac >>
  Cases_on `(a0,e0_num) = (p,d)`
  >- suspend "row_replay_fresh" >>
  asm "off_block" (drule_then (fn th =>
    qpat_assum `FLOOKUP new_blocks (a0,e0_num) = SOME _` (assume_tac o REWRITE_RULE [th]))) >>
  `?old_ms old_es old_ks. FLOOKUP ms_tab (a0,e0_num) = SOME old_ms /\
    FLOOKUP es_tab (a0,e0_num) = SOME old_es /\ FLOOKUP ks_tab (a0,e0_num) = SOME old_ks` by
    (qpat_assum `!a e. (a,e) IN FDOM blocks ==> ?ms ess ks. _` irule >>
     qpat_assum `FLOOKUP blocks (a0,e0_num) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[flookup_thm]) >>
  asm "rows" (drule_then (drule_then (drule_then drule))) >> strip_tac >>
  suspend "row_replay_retained"
QED

Resume dft_packet_pseudo_next_clauses[row_replay_fresh]:
  qpat_assum `(a0,e0_num) = (p,d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  qpat_x_assum `a0 = p` SUBST_ALL_TAC >> qpat_x_assum `e0_num = d` SUBST_ALL_TAC >>
  asm "current_block_next" (fn upd =>
    qpat_x_assum `FLOOKUP new_blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
      (mp_tac o REWRITE_RULE [upd])) >>
  Cases_on `SUC k < LENGTH ps`
  >- (qpat_assum `SUC k < LENGTH ps` (fn th => rewrite_tac
        [th,optionTheory.SOME_11,pairTheory.PAIR_EQ,optionTheory.NOT_NONE_SOME])) >>
  qpat_assum `~(SUC k < LENGTH ps)` (fn th => rewrite_tac
    [th,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (fn th =>
    if is_eq (concl th) then SUBST_ALL_TAC (SYM th) else assume_tac th)) >>
  `ms0 = cm /\ ess0 = ce /\ ks0 = ck` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP ms1 (p,d) = SOME ms0`,`FLOOKUP es1 (p,d) = SOME ess0`,
       `FLOOKUP ks1 (p,d) = SOME ks0`,`FLOOKUP ms_new (p,d) = SOME cm`,
       `FLOOKUP es_new (p,d) = SOME ce`,`FLOOKUP ks_new (p,d) = SOME ck`,
       `Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`,
       `~(SUC k < LENGTH ps)`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[Abbr `ms1`,Abbr `es1`,Abbr `ks1`]) >>
  `s1.vs_inst_idx = LENGTH ps` by
    (qpat_assum `~(SUC k < LENGTH ps) ==> SUC k = LENGTH ps` drule >>
     qpat_assum `s1 = u with vs_inst_idx := SUC k` (fn th => simp_tac (srw_ss()) [th])) >>
  let
    val row_simps =
      map_every (fn pat => qpat_assum pat mp_tac)
        [`ms0 = cm`,`ess0 = ce`,`ks0 = ck`,
         `Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      gvs[Abbr `cm`,Abbr `ce`,Abbr `ck`,LIST_REL_EL_EQN,EL_GENLIST]
    val aligned = row_simps >> gen_tac >> strip_tac >> IF_CASES_TAC >> simp[]
  in
    conj_tac >- row_simps >> conj_tac >- row_simps >> conj_tac >- row_simps >>
    conj_tac >- aligned >> conj_tac >- aligned
  end >>
  conj_tac >- suspend "fresh_row_distinct" >>
  map_every qx_gen_tac [`sf0`,`tf0`,`inc0`,`ent0`,`ord0`,`res0`,`nr0`] >> disch_tac >>
  qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (fn th =>
    qpat_x_assum `FLOOKUP acts p = SOME (sf0,tf0,inc0,ent0,ord0,res0,nr0)`
      (mp_tac o REWRITE_RULE [th])) >>
  simp_tac pure_ss [optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  conj_tac >- suspend "fresh_row_classification" >>
  map_every qx_gen_tac [`fuel`,`n`,`fill`,`tail`] >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE n xs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`EVERY (\i. ~is_terminator i.inst_opcode) (TAKE n xs)`,
       `!q. q < n /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE 0 schedule)`,
       `n <= LENGTH xs`] >>
     rpt (pop_assum kall_tac) >> simp[EVERY_EL, EL_TAKE, LENGTH_TAKE] >> metis_tac[]) >>
  irule (Q.INST [`ms` |-> `ms0:bytes32 option list list`] dft_packet_fresh_row_replay) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`bb.bb_instructions = ps ++ xs`,`s1.vs_inst_idx = LENGTH ps`,
     `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,`n <= LENGTH xs`,
     `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE n xs)`,
     `ms0 = cm`,`ess0 = ce`,`ks0 = ck`,`LIST_REL _ (TAKE n ms0) fill`,
     `Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[Abbr `cm`,Abbr `ce`,Abbr `ck`]
QED

Resume dft_packet_pseudo_next_clauses[fresh_row_distinct]:
  qpat_assum `ks0 = ck` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[fresh_row_classification]:
  qx_gen_tac `r` >> disch_tac >>
  `FLOOKUP calls (p,d,(EL r xs).inst_id) = NONE` by
    (Cases_on `FLOOKUP calls (p,d,(EL r xs).inst_id)` >- simp[] >>
     rename1 `FLOOKUP calls _ = SOME v` >> PairCases_on `v` >>
     asm "call_records" (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,NONE,_,_,_,_)` (fn th =>
       qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
         (mp_tac o REWRITE_RULE [th])) >> simp_tac std_ss []) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`ms0 = cm`,`ess0 = ce`,`ks0 = ck`,`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`,
     `!cid. ALOOKUP obs (p,d,cid) = NONE`,`FLOOKUP calls (p,d,(EL r xs).inst_id) = NONE`,
     `r < LENGTH xs`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  gvs[Abbr `cm`,Abbr `ce`,Abbr `ck`,EL_GENLIST] >>
  Cases_on `(EL r xs).inst_opcode = GAS` >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[row_replay_retained]:
  `LENGTH ms0 = LENGTH old_ms /\ LENGTH ess0 = LENGTH old_es /\
   LENGTH ks0 = LENGTH old_ks` by suspend "retained_lengths" >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  `LIST_REL (\x y. LENGTH x = LENGTH y) ms0 ess0 /\
   LIST_REL (\x y. LENGTH x = LENGTH y) ms0 ks0` by
    suspend "retained_alignment" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "retained_row_distinct" >>
  map_every qx_gen_tac [`sf0`,`tf0`,`inc0`,`ent0`,`ord0`,`res0`,`nr0`] >> disch_tac >>
  conj_tac >- suspend "retained_row_classification" >>
  map_every qx_gen_tac [`fuel`,`n`,`fill`,`tail`] >> strip_tac >>
  let
    fun frame label oldrow newrow =
      asm label (fn th => drule_all_then
        (fn eq => qpat_assum oldrow (fn oldeq => qpat_assum newrow (fn neweq =>
          assume_tac (SIMP_RULE std_ss [oldeq,neweq] eq)))) (cj 1 (cj 2 th)))
  in
    frame "mask_history" `FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`
      `FLOOKUP ms1 (a0,e0_num) = SOME ms0` >>
    frame "site_history" `FLOOKUP es_tab (a0,e0_num) = SOME old_es`
      `FLOOKUP es1 (a0,e0_num) = SOME ess0` >>
    frame "key_history" `FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`
      `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
  end >>
  map_every (fn pat => qpat_assum pat SUBST1_TAC)
    [`TAKE n ms0 = TAKE n old_ms`,`TAKE n ess0 = TAKE n old_es`,
     `TAKE n ks0 = TAKE n old_ks`] >>
  qpat_assum `!sf tf inc entry order res nrest.
    FLOOKUP acts a0 = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    _ /\ (!F k kgss tail. _ ==> _ /\ _)`
    (drule_then (qspecl_then [`fuel`,`n`,`fill`,`tail`] mp_tac o CONJUNCT2)) >>
  (impl_tac >-
    (qpat_assum `TAKE n ms0 = TAKE n old_ms` (fn eq =>
       qpat_assum `LIST_REL _ (TAKE n ms0) fill` (assume_tac o REWRITE_RULE [eq])) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[retained_lengths]:
  Cases_on `?i. i < LENGTH p /\ (a0,e0_num) = (DROP (SUC i) p,FST (EL i p))`
  >- (qpat_x_assum `?i. _ /\ (a0,e0_num) = _` (qx_choose_then `idx` strip_assume_tac) >>
      let
        fun size label oldeq neweq =
          asm label (DISJ_CASES_THEN2
            (fn eq => qpat_assum oldeq (fn old =>
              qpat_assum neweq (mp_tac o REWRITE_RULE [eq,old])))
            (fn th => qpat_assum `(a0,e0_num) = _` (fn key =>
              qpat_assum oldeq (assume_tac o REWRITE_RULE [key]) >>
              qpat_assum neweq (fn eq => qspec_then `idx`
                (drule_all_then (mp_tac o REWRITE_RULE [REWRITE_RULE [key] eq]))
                (CONJUNCT2 th))))) >>
          SIMP_TAC std_ss [optionTheory.SOME_11,LENGTH_LUPDATE] >>
          disch_then SUBST1_TAC >> REFL_TAC
      in
        conj_tac >- size "history_mask_update" `FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`
          `FLOOKUP ms1 (a0,e0_num) = SOME ms0` >>
        conj_tac >- size "history_site_update" `FLOOKUP es_tab (a0,e0_num) = SOME old_es`
          `FLOOKUP es1 (a0,e0_num) = SOME ess0` >>
        size "history_key_update" `FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`
          `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
      end) >>
  `!i. i < LENGTH p ==> (a0,e0_num) <> (DROP (SUC i) p,FST (EL i p))` by
    (qx_gen_tac `idx` >> disch_tac >> disch_tac >>
     qpat_assum `~(?i. _ /\ (a0,e0_num) = _)` (irule o NOT_ELIM) >>
     qexists_tac `idx` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  let
    fun size label oldeq neweq =
      asm label (qspecl_then [`a0`,`e0_num`] (drule_all_then (fn eq =>
        qpat_assum neweq (fn n => qpat_assum oldeq
          (fn oeq => mp_tac (REWRITE_RULE [n,oeq] eq))))) o cj 1) >>
      SIMP_TAC std_ss [optionTheory.SOME_11] >> disch_then SUBST1_TAC >> REFL_TAC
  in
    conj_tac >- size "mask_history" `FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`
      `FLOOKUP ms1 (a0,e0_num) = SOME ms0` >>
    conj_tac >- size "site_history" `FLOOKUP es_tab (a0,e0_num) = SOME old_es`
      `FLOOKUP es1 (a0,e0_num) = SOME ess0` >>
    size "key_history" `FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`
      `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
  end
QED

Resume dft_packet_pseudo_next_clauses[path_alignment]:
  `!i. i <= LENGTH p ==>
    AM1 (DROP i p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP ms1 (DROP i p,f)))) (EL i orders)) /\
    AE1 (DROP i p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP es1 (DROP i p,f)))) (EL i orders)) /\
    AK1 (DROP i p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks1 (DROP i p,f)))) (EL i orders))` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _` drule >>
     strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (AM1 = _)`,`Abbrev (AE1 = _)`,`Abbrev (AK1 = _)`,
        `FLOOKUP acts (DROP i p) = SOME (_,_,_,_,EL i orders,_,_)`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[Abbr `AM1`,Abbr `AE1`,Abbr `AK1`]) >>
  `!i. i <= LENGTH p ==> (!f. MEM f (EL i orders) ==>
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP i p,f))) (THE (FLOOKUP es1 (DROP i p,f))) /\
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP i p,f))) (THE (FLOOKUP ks1 (DROP i p,f)))) ==>
    LENGTH (AM1 (DROP i p)) = LENGTH (AE1 (DROP i p)) /\
    LENGTH (AM1 (DROP i p)) = LENGTH (AK1 (DROP i p))` by
    suspend "aligned_rows_aggregate" >>
  `!i f. i <= LENGTH p /\ (if i = 0 then f <> d else f <> FST (EL (i-1) p)) ==>
    (DROP i p,f) <> (p,d) /\
    (!r. r < LENGTH p ==> (DROP i p,f) <> (DROP (SUC r) p,FST (EL r p)))` by
    suspend "path_other_row" >>
  `!i f. i <= LENGTH p /\ MEM f (EL i orders) /\
      (if i = 0 then f <> d else f <> FST (EL (i-1) p)) ==>
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP i p,f))) (THE (FLOOKUP es1 (DROP i p,f))) /\
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP i p,f))) (THE (FLOOKUP ks1 (DROP i p,f)))` by
    suspend "path_alignment_other" >>
  Induct >- suspend "path_alignment_bottom" >>
  suspend "path_alignment_parent"
QED

Resume dft_packet_pseudo_next_clauses[aligned_rows_aggregate]:
  gen_tac >> strip_tac >> disch_tac >>
  qpat_assum `!i. i <= LENGTH p ==> AM1 (DROP i p) = _ /\ _`
    (drule_then (fn th => pure_rewrite_tac[th])) >>
  let
    fun aggregate rel = simp[NoAsms,LENGTH_FLAT,MAP_MAP_o,combinTheory.o_DEF] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[NoAsms] >>
      qx_gen_tac `f` >> disch_tac >>
      qpat_assum `!f. MEM f (EL i orders) ==> LIST_REL _ _ _ /\ _`
        (drule_then (mp_tac o rel)) >>
      rpt (pop_assum kall_tac) >> simp[LIST_REL_EL_EQN] >> strip_tac >>
      AP_TERM_TAC >> simp[LIST_EQ_REWRITE,EL_MAP]
  in
    conj_tac >- aggregate CONJUNCT1 >> aggregate CONJUNCT2
  end
QED

Resume dft_packet_pseudo_next_clauses[path_other_row]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      `LENGTH (DROP i p) = LENGTH p` by
        (qpat_assum `(DROP i p,f) = (p,d)` (fn th =>
           rewrite_tac [CONJUNCT1 (REWRITE_RULE [pairTheory.PAIR_EQ] th)])) >>
      `i = 0` by (qpat_assum `LENGTH (DROP i p) = LENGTH p` mp_tac >>
                  qpat_assum `i <= LENGTH p` mp_tac >>
                  rpt (pop_assum kall_tac) >> simp[LENGTH_DROP] >> decide_tac) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`if i = 0 then f <> d else _`,`(DROP i p,f) = (p,d)`,`i = 0`] >>
      rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ]) >>
  qx_gen_tac `r` >> disch_tac >> disch_tac >>
  `LENGTH (DROP i p) = LENGTH (DROP (SUC r) p)` by
    (qpat_assum `(DROP i p,f) = (DROP (SUC r) p,FST (EL r p))` (fn th =>
       rewrite_tac [CONJUNCT1 (REWRITE_RULE [pairTheory.PAIR_EQ] th)])) >>
  `i = SUC r` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH (DROP i p) = LENGTH (DROP (SUC r) p)`,`i <= LENGTH p`,`r < LENGTH p`] >>
     rpt (pop_assum kall_tac) >> simp[LENGTH_DROP] >> decide_tac) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`if i = 0 then f <> d else _`,
     `(DROP i p,f) = (DROP (SUC r) p,FST (EL r p))`,`i = SUC r`] >>
  rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ]
QED

Resume dft_packet_pseudo_next_clauses[path_alignment_other]:
  map_every qx_gen_tac [`i`,`f`] >> strip_tac >>
  qpat_assum `!i f. i <= LENGTH p /\ MEM f (EL i orders) ==> ?mr er kr. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!i f. i <= LENGTH p /\ (if i = 0 then _ else _) ==> _`
    (drule_all_then strip_assume_tac) >>
  map_every (fn l => asm l
    (qspecl_then [`DROP i p`,`f`] (drule_all_then SUBST1_TAC) o cj 1))
    ["mask_history","site_history","key_history"] >>
  simp[NoAsms, (* lookup equations only below *)] >>
  map_every (fn pat => qpat_assum pat SUBST1_TAC)
    [`FLOOKUP ms_tab (DROP i p,f) = SOME _`,
     `FLOOKUP es_tab (DROP i p,f) = SOME _`,
     `FLOOKUP ks_tab (DROP i p,f) = SOME _`] >>
  simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[path_alignment_bottom]:
  `LIST_REL (\x y. LENGTH x = LENGTH y)
      (THE (FLOOKUP ms1 (p,d))) (THE (FLOOKUP es1 (p,d))) /\
    LIST_REL (\x y. LENGTH x = LENGTH y)
      (THE (FLOOKUP ms1 (p,d))) (THE (FLOOKUP ks1 (p,d)))` by
    suspend "path_alignment_bottom_special" >>
  `!f. MEM f (EL 0 orders) ==>
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP 0 p,f))) (THE (FLOOKUP es1 (DROP 0 p,f))) /\
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP 0 p,f))) (THE (FLOOKUP ks1 (DROP 0 p,f)))` by
    (qx_gen_tac `f` >> strip_tac >> Cases_on `f = d`
     >- (map_every (fn pat => qpat_assum pat mp_tac)
           [`LIST_REL _ (THE (FLOOKUP ms1 (p,d))) (THE (FLOOKUP ks1 (p,d)))`,
            `LIST_REL _ (THE (FLOOKUP ms1 (p,d))) (THE (FLOOKUP es1 (p,d)))`,`f = d`] >>
         rpt (pop_assum kall_tac) >> simp[]) >>
     qpat_assum `!i f. i <= LENGTH p /\ MEM f (EL i orders) /\ _ ==> _`
       (qspecl_then [`0`,`f`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `!i. i <= LENGTH p ==> (!f. MEM f (EL i orders) ==> _) ==> _`
    (qspec_then `0` mp_tac) >>
  (impl_tac >- simp[NoAsms]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  disch_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[path_alignment_bottom_special]:
  asm "block_records" (drule_then strip_assume_tac) >>
  qpat_assum `(case (NONE:(venom_state # num) option) of NONE => _ | SOME _ => _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.option_case_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`,
     `FLOOKUP ms_new (p,d) = SOME cm`,`FLOOKUP es_new (p,d) = SOME ce`,
     `FLOOKUP ks_new (p,d) = SOME ck`,
     `FLOOKUP ms_tab (p,d) = SOME []`,`FLOOKUP es_tab (p,d) = SOME []`,
     `FLOOKUP ks_tab (p,d) = SOME []`,
     `Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `SUC k < LENGTH ps` >-
    simp[Abbr `ms1`,Abbr `es1`,Abbr `ks1`] >>
  simp[Abbr `ms1`,Abbr `es1`,Abbr `ks1`,Abbr `cm`,Abbr `ce`,Abbr `ck`,
       LIST_REL_EL_EQN,EL_GENLIST] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[path_alignment_parent]:
  rename1 `SUC idx <= LENGTH p ==> _` >> disch_tac >> strip_tac >>
  `idx < LENGTH p /\ idx <= LENGTH p` by
    (qpat_assum `SUC idx <= LENGTH p` mp_tac >> rpt (pop_assum kall_tac) >> decide_tac) >>
  qpat_assum `idx <= LENGTH p ==> LENGTH (AM1 (DROP idx p)) = _ /\ _`
    (drule_then strip_assume_tac) >>
  `LIST_REL (\x y. LENGTH x = LENGTH y)
      (THE (FLOOKUP ms1 (DROP (SUC idx) p,FST (EL idx p))))
      (THE (FLOOKUP es1 (DROP (SUC idx) p,FST (EL idx p)))) /\
    LIST_REL (\x y. LENGTH x = LENGTH y)
      (THE (FLOOKUP ms1 (DROP (SUC idx) p,FST (EL idx p))))
      (THE (FLOOKUP ks1 (DROP (SUC idx) p,FST (EL idx p))))` by
    suspend "path_alignment_parent_special" >>
  `!f. MEM f (EL (SUC idx) orders) ==>
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP (SUC idx) p,f)))
        (THE (FLOOKUP es1 (DROP (SUC idx) p,f))) /\
      LIST_REL (\x y. LENGTH x = LENGTH y)
        (THE (FLOOKUP ms1 (DROP (SUC idx) p,f)))
        (THE (FLOOKUP ks1 (DROP (SUC idx) p,f)))` by
    (qx_gen_tac `f` >> strip_tac >> Cases_on `f = FST (EL idx p)`
     >- (qpat_assum `f = FST (EL idx p)` SUBST1_TAC >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i f. i <= LENGTH p /\ MEM f (EL i orders) /\ _ ==> _`
       (qspecl_then [`SUC idx`,`f`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `!i. i <= LENGTH p ==> (!f. MEM f (EL i orders) ==> _) ==> _`
    (qspec_then `SUC idx` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[path_alignment_parent_special]:
  qpat_assum `!i. i < LENGTH p ==> MEM (FST (EL i p)) (EL (SUC i) orders)`
    (drule_then assume_tac) >>
  qpat_assum `!i f. i <= LENGTH p /\ MEM f (EL i orders) ==> ?mr er kr. _`
    (qspecl_then [`SUC idx`,`FST (EL idx p)`] (drule_all_then strip_assume_tac)) >>
  Cases_on `SUC k < LENGTH ps`
  >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP ms_tab (DROP (SUC idx) p,FST (EL idx p)) = SOME _`,
        `FLOOKUP es_tab (DROP (SUC idx) p,FST (EL idx p)) = SOME _`,
        `FLOOKUP ks_tab (DROP (SUC idx) p,FST (EL idx p)) = SOME _`,
        `LIST_REL _ mr er`,`LIST_REL _ mr kr`,
        `Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`,
        `SUC k < LENGTH ps`] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      simp[Abbr `ms1`,Abbr `es1`,Abbr `ks1`]) >>
  `ms1 = ms_new /\ es1 = es_new /\ ks1 = ks_new` by
    simp[Abbr `ms1`,Abbr `es1`,Abbr `ks1`] >>
  qpat_assum `!i. i <= LENGTH p ==> AM1 (DROP i p) = _ /\ _`
    (qspec_then `idx` (drule_then (EVERY o map (assume_tac o SYM) o CONJUNCTS))) >>
  let
    fun update eq tab result =
      qpat_assum eq (fn th => simp[NoAsms,th]) >>
      qpat_assum tab (fn th => drule_all_then
        (fn rw => qpat_assum result (fn ag => qpat_assum eq (fn e =>
          pure_rewrite_tac [REWRITE_RULE [REWRITE_RULE [e] ag] (cj 1 rw)]))) th)
  in
    update `ms1 = ms_new` `!i rows. i < LENGTH p /\ FLOOKUP ms_tab _ = SOME rows ==> _`
      `FLAT _ = AM1 (DROP idx p)` >>
    update `es1 = es_new` `!i rows. i < LENGTH p /\ FLOOKUP es_tab _ = SOME rows ==> _`
      `FLAT _ = AE1 (DROP idx p)` >>
    update `ks1 = ks_new` `!i rows. i < LENGTH p /\ FLOOKUP ks_tab _ = SOME rows ==> _`
      `FLAT _ = AK1 (DROP idx p)`
  end >>
  simp[NoAsms] >>
  conj_tac >> irule EVERY2_LUPDATE_same >>
  conj_tac >> BETA_TAC >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[retained_alignment]:
  Cases_on `?i. i <= LENGTH p /\ a0 = DROP i p`
  >- (qpat_x_assum `?i. _ /\ a0 = _` (qx_choose_then `idx` strip_assume_tac) >>
      `MEM e0_num (EL idx orders)` by
        (qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _`
           (drule_then strip_assume_tac) >>
         asm "activations" (drule_then assume_tac o cj 7) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`!e. MEM e (EL idx orders) <=> _`,
            `FLOOKUP blocks (a0,e0_num) = SOME _`,`a0 = DROP idx p`] >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[flookup_thm]) >>
      qpat_assum `!i. i <= LENGTH p ==> LENGTH (AM1 (DROP i p)) = _ /\ _ /\ _`
        (qspec_then `idx` (drule_then (drule_then mp_tac o cj 3))) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP ms1 (a0,e0_num) = SOME ms0`,`FLOOKUP es1 (a0,e0_num) = SOME ess0`,
         `FLOOKUP ks1 (a0,e0_num) = SOME ks0`,`a0 = DROP idx p`] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `!i. i < LENGTH p ==> (a0,e0_num) <> (DROP (SUC i) p,FST (EL i p))` by
    (qx_gen_tac `idx` >> strip_tac >> disch_tac >>
     qpat_assum `~(?i. _ /\ a0 = _)` (irule o NOT_ELIM) >> qexists_tac `SUC idx` >>
     qpat_assum `(a0,e0_num) = _` mp_tac >> qpat_assum `idx < LENGTH p` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ]) >>
  let
    fun restore label neweq oldeq =
      asm label (qspecl_then [`a0`,`e0_num`] (drule_all_then (fn eq =>
        qpat_assum neweq (fn n => qpat_assum oldeq (fn oeq =>
          mp_tac (REWRITE_RULE [n,oeq] eq))))) o cj 1) >>
      SIMP_TAC std_ss [optionTheory.SOME_11] >> disch_then SUBST1_TAC
  in
    restore "mask_history" `FLOOKUP ms1 (a0,e0_num) = SOME ms0`
      `FLOOKUP ms_tab (a0,e0_num) = SOME old_ms` >>
    restore "site_history" `FLOOKUP es1 (a0,e0_num) = SOME ess0`
      `FLOOKUP es_tab (a0,e0_num) = SOME old_es` >>
    restore "key_history" `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
      `FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`
  end >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[path_row_distinct]:
  map_every qx_gen_tac [`idx`,`visit`] >> strip_tac >>
  `AK1 (DROP idx p) = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks1 (DROP idx p,f))))
    (EL idx orders))` by
    (qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `Abbrev (AK1 = _)` mp_tac >>
     qpat_assum `FLOOKUP acts (DROP idx p) = SOME (_,_,_,_,EL idx orders,_,_)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[Abbr `AK1`]) >>
  qpat_assum `ALL_DISTINCT (AK1 (DROP idx p))` (fn th =>
    qpat_assum `AK1 (DROP idx p) = _` (mp_tac o C EQ_MP th o AP_TERM ``ALL_DISTINCT:gas_event list -> bool``)) >>
  qpat_assum `MEM visit (EL idx orders)` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  drule_all_then (ACCEPT_TAC o BETA_RULE) venomWfPropsTheory.all_distinct_flat_map_member
QED

Resume dft_packet_pseudo_next_clauses[path_aggregate_distinct]:
  `!i. i < LENGTH p /\ ALL_DISTINCT (AK1 (DROP (SUC i) p)) ==>
    ALL_DISTINCT (AK1 (DROP i p))` by suspend "path_distinct_step" >>
  `!n i. i + n = LENGTH p ==> ALL_DISTINCT (AK1 (DROP i p))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!i. i < LENGTH p /\ ALL_DISTINCT (AK1 (DROP (SUC i) p)) ==> _`,
        `ALL_DISTINCT (AK1 [])`] >>
     rpt (pop_assum kall_tac) >> rpt disch_tac >>
     Induct >- simp[rich_listTheory.DROP_LENGTH_NIL] >>
     qx_gen_tac `idx` >> disch_tac >>
     `idx < LENGTH p /\ SUC idx + n = LENGTH p` by decide_tac >>
     qpat_assum `!i. i + n = LENGTH p ==> _` (drule_then assume_tac) >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  qx_gen_tac `idx` >> strip_tac >>
  qpat_assum `!n i. i + n = LENGTH p ==> _`
    (qspecl_then [`LENGTH p - idx`,`idx`] mp_tac) >>
  qpat_assum `idx <= LENGTH p` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[path_distinct_step]:
  qx_gen_tac `idx` >> strip_tac >>
  qpat_assum `!i. i < LENGTH p ==> MEM (FST (EL i p)) (EL (SUC i) orders)`
    (drule_then assume_tac) >>
  `idx <= LENGTH p /\ SUC idx <= LENGTH p` by
    (qpat_assum `idx < LENGTH p` mp_tac >> rpt (pop_assum kall_tac) >> decide_tac) >>
  qpat_assum `!i f. i <= LENGTH p /\ MEM f (EL i orders) /\ ALL_DISTINCT _ ==> _`
    (drule_all_then assume_tac) >>
  qpat_assum `!i. i < LENGTH p ==> ?mr er kr. _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _`
    (drule_then strip_assume_tac) >>
  `EL (EL idx inds) (THE (FLOOKUP ks1 (DROP (SUC idx) p,FST (EL idx p)))) =
    AK1 (DROP idx p) /\
    EL idx inds < LENGTH (THE (FLOOKUP ks1 (DROP (SUC idx) p,FST (EL idx p))))` by
    suspend "path_distinct_cell" >>
  qpat_assum `EL (EL idx inds) _ = AK1 (DROP idx p)` (SUBST1_TAC o SYM) >>
  irule venomFnInstsProofsTheory.all_distinct_flat_mem >>
  goal_assum (drule_at Any) >>
  irule EL_MEM >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[path_distinct_cell]:
  qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _`
    (qspec_then `idx` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  asm "history_key_update" (DISJ_CASES_THEN2 assume_tac
    (fn th => drule_all_then SUBST1_TAC (CONJUNCT2 th)))
  >- (asm "AKeq" mp_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`Abbrev (AK1 = _)`,`ks1 = ks_tab`,
         `FLOOKUP ks_tab (DROP (SUC idx) p,FST (EL idx p)) = SOME kr`,
         `EL idx inds < LENGTH kr`,`EL (EL idx inds) kr = AK (DROP idx p)`] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[Abbr `AK1`]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`Abbrev (AK1 = _)`, `FLOOKUP acts (DROP idx p) = SOME (_,_,_,_,EL idx orders,_,_)`,
     `EL idx inds < LENGTH kr`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[Abbr `AK1`,EL_LUPDATE]
QED

Resume dft_packet_pseudo_next_clauses[retained_row_distinct]:
  Cases_on `?i. i <= LENGTH p /\ a0 = DROP i p`
  >- (qpat_x_assum `?i. _ /\ a0 = _` (qx_choose_then `idx` strip_assume_tac) >>
      `MEM e0_num (EL idx orders)` by
        (qpat_assum `!i. i <= LENGTH p ==> ?sfi tfi inci enti resi nresti. _`
           (drule_then strip_assume_tac) >>
         asm "activations" (drule_then assume_tac o cj 7) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`!e. MEM e (EL idx orders) <=> _`,
            `FLOOKUP blocks (a0,e0_num) = SOME _`,`a0 = DROP idx p`] >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[flookup_thm]) >>
      qpat_assum `!i. i <= LENGTH p ==> ALL_DISTINCT (AK1 (DROP i p))`
        (drule_then assume_tac) >>
      qpat_assum `!i f. i <= LENGTH p /\ MEM f (EL i orders) /\ ALL_DISTINCT _ ==> _`
        (drule_all_then mp_tac) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP ks1 (a0,e0_num) = SOME ks0`,`a0 = DROP idx p`] >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `!i. i < LENGTH p ==> (a0,e0_num) <> (DROP (SUC i) p,FST (EL i p))` by
    (qx_gen_tac `idx` >> strip_tac >> disch_tac >>
     qpat_assum `~(?i. _ /\ a0 = _)` (irule o NOT_ELIM) >> qexists_tac `SUC idx` >>
     qpat_assum `(a0,e0_num) = _` mp_tac >> qpat_assum `idx < LENGTH p` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ]) >>
  asm "key_history" (qspecl_then [`a0`,`e0_num`] (drule_all_then mp_tac) o cj 1) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP ks1 (a0,e0_num) = SOME ks0`,`FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`,
     `ALL_DISTINCT (FLAT old_ks)`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]
QED

Resume dft_packet_pseudo_next_clauses[retained_row_classification]:
  qx_gen_tac `r` >> disch_tac >>
  `~((EL r xs0).inst_opcode = INVOKE /\
     IS_SOME (FLOOKUP calls (a0,e0_num,(EL r xs0).inst_id))) ==>
    EL r ms0 = EL r old_ms /\ EL r ess0 = EL r old_es /\ EL r ks0 = EL r old_ks` by
    suspend "retained_ordinary_cell" >>
  qpat_assum `!sf tf inc entry order res nrest.
    FLOOKUP acts a0 = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    _ /\ (!F k kgss tail. _ ==> _ /\ _)`
    (drule_then (drule_then (mk_asm "old_cell") o CONJUNCT1)) >>
  Cases_on `(EL r xs0).inst_opcode = INVOKE`
  >- (Cases_on `FLOOKUP calls (a0,e0_num,(EL r xs0).inst_id)`
      >- suspend "retained_unrecorded_invoke" >>
      suspend "retained_recorded_invoke") >>
  suspend "retained_noninvoke"
QED

Resume dft_packet_pseudo_next_clauses[retained_recorded_invoke]:
  rename1 `FLOOKUP calls (a0,e0_num,(EL r xs0).inst_id) = SOME recd` >>
  PairCases_on `recd` >>
  `recd0 = r` by suspend "retained_recorded_index" >>
  let
    fun recorded label row =
      asm label (qspecl_then [`a0`,`e0_num`,`(EL r xs0).inst_id`]
        (drule_then (fn th => qpat_assum row (fn eq =>
          assume_tac (SIMP_RULE std_ss [eq,optionTheory.SOME_11] th)))) o cj 8)
  in
    recorded "mask_history" `FLOOKUP ms1 (a0,e0_num) = SOME ms0` >>
    recorded "site_history" `FLOOKUP es1 (a0,e0_num) = SOME ess0` >>
    recorded "key_history" `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
  end >>
  qpat_assum `recd0 = r` (fn eq =>
    map_every (fn pat => qpat_assum pat (mp_tac o REWRITE_RULE [eq]))
      [`recd0 < LENGTH ms0 /\ _`,`recd0 < LENGTH ess0 /\ _`,`recd0 < LENGTH ks0 /\ _`]) >>
  qpat_assum `(EL r xs0).inst_opcode = INVOKE` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[retained_recorded_index]:
  asm "history_call_cells" (qspecl_then [`a0`,`e0_num`,`(EL r xs0).inst_id`]
    (drule_then (qx_choose_then `mr` strip_assume_tac)) o cj 1) >>
  `recd0 < LENGTH xs0 /\ (EL recd0 xs0).inst_id = (EL r xs0).inst_id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`,
        `FLOOKUP ms_tab (a0,e0_num) = SOME mr`, `recd0 < LENGTH mr`,
        `LENGTH old_ms = LENGTH xs0`, `(EL r xs0).inst_id = _`,
        `FLOOKUP blocks (a0,e0_num) = SOME _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs0)` by suspend "retained_id_distinct" >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`ALL_DISTINCT (MAP (\i. i.inst_id) xs0)`,`recd0 < LENGTH xs0`,
     `r < LENGTH xs0`,`(EL recd0 xs0).inst_id = (EL r xs0).inst_id`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  qspecl_then [`MAP (\i. i.inst_id) xs0`,`recd0`,`r`] mp_tac ALL_DISTINCT_EL_IMP >>
  simp[EL_MAP]
QED

Resume dft_packet_pseudo_next_clauses[retained_id_distinct]:
  asm "block_records" (qspecl_then [`a0`,`e0_num`] drule) >> strip_tac >>
  rename1 `lookup_block bb0.bb_label bsf.fn_blocks = SOME bb0` >>
  asm "activations" (qspecl_then [`a0`,`bsf`] (drule_then assume_tac) o cj 3) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`dft_fn_rel bsf btf`, `lookup_block bb0.bb_label bsf.fn_blocks = SOME bb0`,
     `bb0.bb_instructions = ps0 ++ xs0`] >>
  rpt (pop_assum kall_tac) >>
  simp[dft_fn_rel_def,venomWfTheory.wf_function_def,
    venomWfTheory.fn_inst_ids_distinct_def] >> rpt strip_tac >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  drule venomWfPropsTheory.all_distinct_flat_map_member >> disch_then drule >>
  simp[MAP_APPEND,ALL_DISTINCT_APPEND]
QED

Resume dft_packet_pseudo_next_clauses[retained_unrecorded_invoke]:
  asm "old_cell" mp_tac >>
  qpat_assum `~(_ /\ IS_SOME _) ==> _` mp_tac >>
  qpat_assum `FLOOKUP calls (a0,e0_num,(EL r xs0).inst_id) = NONE` mp_tac >>
  qpat_assum `(EL r xs0).inst_opcode = INVOKE` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[retained_noninvoke]:
  asm "old_cell" mp_tac >>
  qpat_assum `~(_ /\ IS_SOME _) ==> _` mp_tac >>
  qpat_assum `(EL r xs0).inst_opcode <> INVOKE` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >> simp[]
QED


Resume dft_packet_pseudo_next_clauses[retained_ordinary_cell]:
  disch_tac >>
  Cases_on `?i. i < LENGTH p /\ (a0,e0_num) = (DROP (SUC i) p,FST (EL i p))`
  >- (qpat_x_assum `?i. _ /\ (a0,e0_num) = _` (qx_choose_then `idx` strip_assume_tac) >>
      `r <> EL idx inds` by suspend "retained_ordinary_not_selected" >>
      suspend "retained_ordinary_live_row") >>
  `!i. i < LENGTH p ==> (a0,e0_num) <> (DROP (SUC i) p,FST (EL i p))` by
    (qx_gen_tac `idx` >> disch_tac >> disch_tac >>
     qpat_assum `~(?i. _ /\ (a0,e0_num) = _)` (irule o NOT_ELIM) >>
     qexists_tac `idx` >> conj_tac >> first_assum ACCEPT_TAC) >>
  let
    fun frame label oldeq neweq =
      asm label (qspecl_then [`a0`,`e0_num`] (drule_all_then (fn eq =>
        qpat_assum neweq (fn n => qpat_assum oldeq
          (fn oeq => mp_tac (REWRITE_RULE [n,oeq] eq))))) o cj 1) >>
      SIMP_TAC std_ss [optionTheory.SOME_11] >> disch_then SUBST1_TAC >> REFL_TAC
  in
    conj_tac >- frame "mask_history" `FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`
      `FLOOKUP ms1 (a0,e0_num) = SOME ms0` >>
    conj_tac >- frame "site_history" `FLOOKUP es_tab (a0,e0_num) = SOME old_es`
      `FLOOKUP es1 (a0,e0_num) = SOME ess0` >>
    frame "key_history" `FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`
      `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
  end
QED

Resume dft_packet_pseudo_next_clauses[retained_ordinary_live_row]:
  let
    fun cell label oldeq neweq =
      asm label (DISJ_CASES_THEN2
        (fn eq => qpat_assum oldeq (fn old =>
          qpat_assum neweq (mp_tac o REWRITE_RULE [eq,old])))
        (fn th => qpat_assum `(a0,e0_num) = _` (fn key =>
          qpat_assum oldeq (assume_tac o REWRITE_RULE [key]) >>
          qpat_assum neweq (fn eq => qspec_then `idx`
            (drule_all_then (mp_tac o REWRITE_RULE [REWRITE_RULE [key] eq]))
              (CONJUNCT2 th))))) >>
      SIMP_TAC std_ss [optionTheory.SOME_11] >> disch_then SUBST1_TAC >>
      simp[EL_LUPDATE]
  in
    conj_tac >- cell "history_mask_update" `FLOOKUP ms_tab (a0,e0_num) = SOME old_ms`
      `FLOOKUP ms1 (a0,e0_num) = SOME ms0` >>
    conj_tac >- cell "history_site_update" `FLOOKUP es_tab (a0,e0_num) = SOME old_es`
      `FLOOKUP es1 (a0,e0_num) = SOME ess0` >>
    cell "history_key_update" `FLOOKUP ks_tab (a0,e0_num) = SOME old_ks`
      `FLOOKUP ks1 (a0,e0_num) = SOME ks0`
  end
QED

Resume dft_packet_pseudo_next_clauses[retained_ordinary_not_selected]:
  disch_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done_at_call child_entry call_h. _`
    (drule_then strip_assume_tac) >>
  asm "history_call_cells" (qspecl_then [`DROP (SUC idx) p`,`FST (EL idx p)`,`SND (EL idx p)`]
    (drule_then (qx_choose_then `mr` strip_assume_tac)) o cj 1) >>
  rename1 `FLOOKUP blocks (DROP (SUC idx) p,FST (EL idx p)) = SOME (_,_,_,parent_xs,_,_,_,_,_,_,_,_,_)` >>
  `parent_xs = xs0` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`(a0,e0_num) = _`,
       `FLOOKUP blocks (a0,e0_num) = SOME _`,
       `FLOOKUP blocks (DROP (SUC idx) p,FST (EL idx p)) = SOME _`] >>
     rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ] >> rpt strip_tac >> gvs[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`~(_ /\ IS_SOME _)`,`r = EL idx inds`,`parent_xs = xs0`,
     `(EL (EL idx inds) parent_xs).inst_opcode = INVOKE`,
     `SND (EL idx p) = _`, `(a0,e0_num) = _`,
     `FLOOKUP calls (DROP (SUC idx) p,FST (EL idx p),SND (EL idx p)) = SOME _`,
     `FLOOKUP blocks (DROP (SUC idx) p,FST (EL idx p)) = SOME _`] >>
  rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ] >> rpt strip_tac >> gvs[] >>
  qpat_assum `SND (EL idx p) = _` (SUBST1_TAC o SYM) >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[rooted_cuts_next]:
  map_every qx_gen_tac [`a0`,`e0_num`,`sf0`,`tf0`,`inc0`,`entry0`,`order0`,`res0`,`nrest0`,
    `bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`in0`,`h00`,`body0`,`count0`,`front0`,`closed0`,`rest0`,`q0`,`z0`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Q_TAC ASM_CASES_TAC `(a0,e0_num) = (p,d)` >- suspend "current_cut_next" >>
  `FLOOKUP new_blocks (a0,e0_num) = FLOOKUP blocks (a0,e0_num)` by
    (asm "off_block" irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `FLOOKUP new_blocks (a0,e0_num) = FLOOKUP blocks (a0,e0_num)` (fn th =>
    qpat_assum `FLOOKUP new_blocks (a0,e0_num) = SOME _` (assume_tac o REWRITE_RULE [th])) >>
  qpat_assum `IS_SOME body0 /\ _ \/ _` (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
  >- suspend "retained_cut_next" >>
  qpat_assum `(a0,e0_num) <> (p,d)` mp_tac >>
  qpat_assum `a0 = p` SUBST1_TAC >> qpat_assum `e0_num = d` SUBST1_TAC >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[retained_cut_next]:
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `((IS_SOME body0 /\ q0 < LENGTH xs0 /\
      z0 = DROP (phi_prefix_length bb0.bb_instructions) ps0 ++ TAKE q0 xs0 /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q0 xs0) /\
      (!r. r < q0 /\ (EL r xs0).inst_opcode = INVOKE ==> MEM r (TAKE count0 rho0))) \/
     (body0 = NONE /\ a0 = p /\ e0_num = d /\ q0 = 0 /\
      z0 = DROP (phi_prefix_length bb0.bb_instructions) (TAKE s.vs_inst_idx ps0)))`
  >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "old_rooted_cuts" (drule_at (Pat `FLOOKUP blocks _ = SOME _`)) >>
  disch_then drule_all >>
  disch_then (qx_choose_then `cuts` (qx_choose_then `levels`
    (qx_choose_then `Mcut` (qx_choose_then `Ecut` (qx_choose_then `Kcut`
    (qx_choose_then `mr` (qx_choose_then `er` (qx_choose_then `kr`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))))) >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "retained_cut_shape"))
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then ai = a0 /\ ei = e0_num /\ qi = q0 /\ zi = z0 /\
        IS_SOME bei /\ qi < LENGTH xsi /\
        EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
        (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi))
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call))`
    >- suspend "retained_cut_shape") >>
  `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order)` by
    (asm "activations" (fn th => map_every (assume_tac o (fn i => cj i th)) [5,6]) >>
     rpt gen_tac >> strip_tac >> conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  `!i. i < LENGTH p ==>
    ?sf tf inc ent ord.
      FLOOKUP acts (DROP (SUC i) p) = SOME (sf,tf,inc,ent,ord,NONE,NONE) /\
      LAST ord = FST (EL i p)` by
    (gen_tac >> strip_tac >> asm "parents" (drule_then strip_assume_tac) >>
     qpat_assum `a = DROP (SUC i) p` (fn eq =>
       qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any o REWRITE_RULE [eq])) >>
     qpat_assum `(e,cid) = EL i p` (mp_tac o Q.AP_TERM `FST`) >>
     qpat_assum `LAST _ = e` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_assum `Abbrev (new_blocks = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `acts = acts` by REFL_TAC >> `calls = calls` by REFL_TAC >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "history_row_lengths"))
    `!a e bb bt ps xs ys rho hin h be hbe pos front closed brest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,brest) ==>
      (?row. FLOOKUP ms_tab (a,e) = SOME row /\ LENGTH row = LENGTH xs) /\
      (?row. FLOOKUP es_tab (a,e) = SOME row /\ LENGTH row = LENGTH xs) /\
      (?row. FLOOKUP ks_tab (a,e) = SOME row /\ LENGTH row = LENGTH xs)`
    >- suspend "history_row_lengths") >>
  let
    fun prefix row update i eqname =
      asm "history_row_lengths" (assume_tac o cj i) >>
      asm "history_call_cells" (assume_tac o cj i) >>
      asm eqname assume_tac >>
      irule dft_packet_pseudo_history_root_prefix >>
      asm update (irule_at Any) >>
      qpat_assum `new_blocks = blocks |+ _` (irule_at Any) >>
      qpat_assum `MAP _ cuts = REVERSE (GENLIST (\i. DROP i a0) _)` (irule_at Any) >>
      qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (irule_at Any) >>
      qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,NONE,0,OK s,F,NONE)` (irule_at Any) >>
      qpat_assum `acts = acts` (irule_at Any) >>
      qpat_assum `calls = calls` (irule_at Any) >>
      qpat_assum row (irule_at Any) >>
      qexistsl [`z0`,`q0`,`e0_num`] >>
      asm "retained_cut_shape" assume_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC
  in
    (`?rest. AM1 [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) ++ rest` by
      prefix `AM = _` "history_mask_update" 1 "AMeq") >>
    (`?rest. AE1 [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) ++ rest` by
      prefix `AE = _` "history_site_update" 2 "AEeq") >>
    (`?rest. AK1 [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) ++ rest` by
      prefix `AK = _` "history_key_update" 3 "AKeq")
  end >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "retained_masks"))
    `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms1 (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ms1 (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))`
    >- suspend "retained_masks") >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "retained_sites"))
    `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es1 (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP es1 (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))`
    >- suspend "retained_sites") >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "retained_keys"))
    `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks1 (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ks1 (ai,ei)))) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
        FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))`
    >- suspend "retained_keys") >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "retained_preceding_blocks"))
    `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      !f. MEM f ds ==>
        FST (THE (FLOOKUP new_blocks (ai,f))) = FST (THE (FLOOKUP blocks (ai,f)))`
    >- suspend "retained_preceding_blocks") >>
  suspend "retained_cut_apply"
QED

Resume dft_packet_pseudo_next_clauses[retained_cut_shape]:
  map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,
    `bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`counti`,`fronti`,`closedi`,`resti`,`later`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  Cases_on `SUC i = LENGTH cuts`
  >- (qpat_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >>
      simp_tac std_ss [Once (DECIDE ``!b:bool. (if T then b else F) = b``)] >>
      asm_rewrite_tac[] >> strip_tac >>
      `xsi = xs0 /\ bei = body0 /\ counti = count0 /\ rhoi = rho0` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`FLOOKUP blocks (ai,ei) = SOME _`,`FLOOKUP blocks (a0,e0_num) = SOME _`,
           `ai = a0`,`ei = e0_num`] >>
         rpt (pop_assum kall_tac) >> strip_tac >> strip_tac >> simp[] >> strip_tac >> simp[]) >>
      asm_rewrite_tac[]) >>
  qpat_assum `SUC i <> LENGTH cuts` (fn neg =>
    qpat_assum `if SUC i = LENGTH cuts then _ else _`
      (mp_tac o REWRITE_RULE [neg]) >> REWRITE_TAC [neg]) >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[history_row_lengths]:
  map_every qx_gen_tac [`ca`,`ce_num`,`cb`,`ct`,`cps`,`cxs`,`cys`,`crho`,
    `hin`,`ch`,`be0`,`hbe0`,`cpos`,`cfront`,`cclosed`,`crest`] >>
  disch_tac >>
  `?mr er kr. FLOOKUP ms_tab (ca,ce_num) = SOME mr /\
    FLOOKUP es_tab (ca,ce_num) = SOME er /\ FLOOKUP ks_tab (ca,ce_num) = SOME kr` by
    (qpat_assum `!a e. (a,e) IN FDOM blocks ==> ?ms ess ks. _` irule >>
     qpat_assum `FLOOKUP blocks (ca,ce_num) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[flookup_thm]) >>
  asm "rows" (fn th => map_every (fn i => drule_all_then assume_tac (cj i th)) [1,2,3]) >>
  rpt conj_tac >> simp[]
QED


local
  fun retained_frame j i eqname update oldeq neweq =
    map_every qx_gen_tac [`idx`,`path_i`,`ds_i`,`depth_i`,`pos_i`,`z_i`] >>
    disch_then (CONJUNCTS_THEN assume_tac) >>
    asm "history_call_cells" (assume_tac o cj i) >>
    asm eqname assume_tac >>
    irule (cj j dft_packet_pseudo_history_cut_frame) >>
    qpat_assum `EL idx cuts = (path_i,ds_i,depth_i,pos_i,z_i)` (irule_at Any) >>
    asm update (irule_at Any) >>
    qpat_assum `new_blocks = blocks |+ _` (irule_at Any) >>
    qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (irule_at Any) >>
    qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,NONE,0,OK s,F,NONE)` (irule_at Any) >>
    qpat_assum `acts = acts` (irule_at Any) >>
    qpat_assum `calls = calls` (irule_at Any) >>
    qpat_assum oldeq (irule_at Any) >>
    qpat_assum neweq (irule_at Any) >>
    qexistsl [`z0`,`q0`,`e0_num`,`a0`] >>
    asm "retained_cut_shape" assume_tac >>
    rpt conj_tac >> first_assum ACCEPT_TAC
in
Resume dft_packet_pseudo_next_clauses[retained_masks]:
  retained_frame 6 1 "AMeq" "history_mask_update" `AM = _` `AM1 = _`
QED

Resume dft_packet_pseudo_next_clauses[retained_sites]:
  retained_frame 6 2 "AEeq" "history_site_update" `AE = _` `AE1 = _`
QED

Resume dft_packet_pseudo_next_clauses[retained_keys]:
  retained_frame 6 3 "AKeq" "history_key_update" `AK = _` `AK1 = _`
QED
end

Resume dft_packet_pseudo_next_clauses[retained_preceding_blocks]:
  rpt gen_tac >> disch_tac >>
  qx_gen_tac `prior_depth` >> disch_tac >>
  Q_TAC ASM_CASES_TAC `(ai,prior_depth) = (p,d)`
  >- (qpat_assum `(ai,prior_depth) = (p,d)` SUBST1_TAC >>
      qpat_assum `new_blocks = blocks |+ _` (fn eq =>
        qpat_assum `FLOOKUP blocks (p,d) = SOME _` (fn old =>
          simp[NoAsms,eq,old,FLOOKUP_UPDATE]))) >>
  asm "off_block" (drule_then SUBST1_TAC) >> REFL_TAC
QED

Resume dft_packet_pseudo_next_clauses[retained_cut_apply]:
  qmatch_asmsub_rename_tac `AM1 [] = _ ++ mr1` >>
  qmatch_asmsub_rename_tac `AE1 [] = _ ++ er1` >>
  qmatch_asmsub_rename_tac `AK1 [] = _ ++ kr1` >>
  qexistsl [`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr1`,`er1`,`kr1`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- suspend "retained_cut_records") >>
  (conj_tac >- suspend "retained_cut_mask_flat") >>
  (conj_tac >- suspend "retained_cut_site_flat") >>
  (conj_tac >- suspend "retained_cut_key_flat") >>
  map_every (fn pat => conj_tac >- (qpat_assum pat SUBST1_TAC >> first_assum ACCEPT_TAC))
    [`Mcut = FLAT (MAP _ cuts)`,`Ecut = FLAT (MAP _ cuts)`,`Kcut = FLAT (MAP _ cuts)`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "retained_cut_eval"
QED

local
  fun cut_flat label eq =
    qpat_assum eq SUBST1_TAC >>
    AP_TERM_TAC >> simp[NoAsms,Once LIST_EQ_REWRITE,EL_MAP] >>
    qx_gen_tac `idx` >> disch_tac >>
    qabbrev_tac `cut_tuple = EL idx cuts` >> PairCases_on `cut_tuple` >>
    qpat_assum `Abbrev ((_,_,_,_,_) = EL idx cuts)`
      (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
    simp[NoAsms] >> sym_tac >> asm label irule >>
    goal_assum (drule_at Any) >> first_assum ACCEPT_TAC
in
Resume dft_packet_pseudo_next_clauses[retained_cut_mask_flat]:
  cut_flat "retained_masks" `Mcut = FLAT (MAP _ cuts)`
QED
Resume dft_packet_pseudo_next_clauses[retained_cut_site_flat]:
  cut_flat "retained_sites" `Ecut = FLAT (MAP _ cuts)`
QED
Resume dft_packet_pseudo_next_clauses[retained_cut_key_flat]:
  cut_flat "retained_keys" `Kcut = FLAT (MAP _ cuts)`
QED
end

Resume dft_packet_pseudo_next_clauses[retained_cut_eval]:
  `body0 <> NONE /\ ~(a0 = p /\ e0_num = d)` by
    (qpat_assum `IS_SOME body0` mp_tac >>
     qpat_assum `(a0,e0_num) <> (p,d)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[optionTheory.IS_SOME_EQ_NOT_NONE]) >>
  map_every qx_gen_tac [`F_eval`,`gs_eval`,`tail_eval`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`
    (qspecl_then [`F_eval`,`gs_eval`,`tail_eval`] (drule_all_then mp_tac)) >>
  qpat_assum `body0 <> NONE` (fn neq =>
    qpat_assum `~(a0 = p /\ e0_num = d)` (fn off =>
      simp_tac (bool_ss ++ boolSimps.CONJ_ss) [neq,off,CONJ_ASSOC]))
QED

Resume dft_packet_pseudo_next_clauses[retained_cut_records]:
  map_every qx_gen_tac [`idx`,`ai`,`ds`,`ei`,`qi`,`zi`] >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  `FLOOKUP new_blocks (ai,ei) = FLOOKUP blocks (ai,ei)` by
    (asm "off_block" irule >>
     Cases_on `SUC idx = LENGTH cuts`
     >- (qpat_assum `SUC idx = LENGTH cuts` (fn eq =>
           qpat_assum `if SUC idx = LENGTH cuts then _ else _`
             (mp_tac o REWRITE_RULE [eq])) >>
         qpat_assum `(a0,e0_num) <> (p,d)` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ]) >>
     qpat_assum `SUC idx <> LENGTH cuts` (fn ne =>
       qpat_assum `if SUC idx = LENGTH cuts then _ else _`
         (strip_assume_tac o REWRITE_RULE [ne])) >>
     asm "call_records" (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[pairTheory.PAIR_EQ] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,
    `bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,`bei`,`counti`,`fronti`,`closedi`,`resti`,`later`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- asm_rewrite_tac[]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EL idx levels = _` SUBST1_TAC >>
  simp[NoAsms,pairTheory.pair_CASE_def] >>
  irule MAP_CONG >> simp[NoAsms] >>
  qx_gen_tac `prior_depth` >> disch_tac >>
  asm "retained_preceding_blocks" (qspecl_then [`idx`,`ai`,`ds`,`ei`,`qi`,`zi`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspec_then `prior_depth` (drule_then SUBST1_TAC)) >> simp[NoAsms]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_next]:
  qpat_x_assum `(a0,e0_num) = (p,d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  qpat_assum `a0 = p` SUBST_ALL_TAC >> qpat_assum `e0_num = d` SUBST_ALL_TAC >>
  asm "current_block_next" (fn th =>
    qpat_x_assum `FLOOKUP new_blocks (p,d) = SOME (bb0,bt0,_,_,_,_,_,_,_,_,_,_,_)`
      (strip_assume_tac o REWRITE_RULE [th,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC o SYM))
    [`bb = bb0`,`bt = bt0`,`ps = ps0`,`xs = xs0`,`ys = ys0`,`schedule = rho0`,
     `in_state = in0`,`h0 = h00`,`0 = count0`,
     `(if SUC k < LENGTH ps then NONE else SOME (s1,SUC j)) = body0`] >>
  qabbrev_tac `zold = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps)` >>
  asm "old_rooted_cuts" (qspecl_then
    [`p`,`d`,`sf`,`fn`,`inc`,`entry`,`order`,`NONE`,`NONE`,`bb`,`bt`,`ps`,`xs`,`ys`,
     `schedule`,`in_state`,`h0`,`NONE`,`0`,`OK s`,`F`,`NONE`,`0`,`zold`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms,Abbr `zold`])) >>
  disch_then (qx_choose_then `cuts` (qx_choose_then `levels`
    (qx_choose_then `Mcut` (qx_choose_then `Ecut` (qx_choose_then `Kcut`
    (qx_choose_then `mr` (qx_choose_then `er` (qx_choose_then `kr`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))))) >>
  `cuts <> []` by
    (qpat_assum `MAP _ cuts = REVERSE _` mp_tac >>
     Cases_on `cuts` >> simp[NoAsms,EQ_SYM_EQ,GENLIST_EQ_NIL]) >>
  `levels <> []` by
    (qpat_assum `LENGTH cuts = LENGTH levels` mp_tac >>
     qpat_assum `cuts <> []` mp_tac >> Cases_on `levels` >>
     simp[NoAsms,LENGTH_NIL]) >>
  qabbrev_tac `cut_pre = FRONT cuts` >>
  qabbrev_tac `level_pre = FRONT levels` >>
  `cut_pre ++ [LAST cuts] = cuts` by
    (simp[NoAsms,Abbr `cut_pre`] >> irule APPEND_FRONT_LAST >> first_assum ACCEPT_TAC) >>
  `level_pre ++ [LAST levels] = levels` by
    (simp[NoAsms,Abbr `level_pre`] >> irule APPEND_FRONT_LAST >> first_assum ACCEPT_TAC) >>
  `SUC (LENGTH cut_pre) = LENGTH cuts` by
    (qpat_assum `cut_pre ++ [_] = cuts` (mp_tac o AP_TERM ``LENGTH : (((num # num) list # num list # num # num # instruction list) list) -> num``) >>
     simp[NoAsms]) >>
  `LENGTH cut_pre = LENGTH level_pre` by
    (qpat_assum `LENGTH cuts = LENGTH levels` mp_tac >>
     qpat_assum `cuts <> []` mp_tac >> qpat_assum `levels <> []` mp_tac >>
     simp[NoAsms,Abbr `cut_pre`,Abbr `level_pre`,LENGTH_FRONT]) >>
  qabbrev_tac `lastcut = LAST cuts` >> PairCases_on `lastcut` >>
  suspend "current_cut_unpack"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_unpack]:
  `EL (LENGTH cut_pre) cuts = (lastcut0,lastcut1,lastcut2,lastcut3,lastcut4)` by
    (qpat_assum `cut_pre ++ [_] = cuts` (SUBST1_TAC o SYM) >>
     simp[NoAsms,rich_listTheory.EL_LENGTH_APPEND]) >>
  `LENGTH cut_pre < LENGTH cuts` by
    (qpat_assum `SUC (LENGTH cut_pre) = LENGTH cuts` (SUBST1_TAC o SYM) >> simp[NoAsms]) >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `SUC (LENGTH cut_pre) = LENGTH cuts` (fn eq =>
    qpat_x_assum `if SUC (LENGTH cut_pre) = LENGTH cuts then _ else _`
      (strip_assume_tac o REWRITE_RULE [eq])) >>
  map_every (fn pat => qpat_assum pat SUBST_ALL_TAC)
    [`lastcut0 = p`,`lastcut2 = d`,`lastcut3 = 0`,`lastcut4 = zold`] >>
  suspend "current_cut_last_row"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_last_row]:
  `sfi = sf /\ orderi = order /\ bbi = bb` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP acts p = SOME (sfi,_,_,_,_,_,_)`,
       `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)`,
       `FLOOKUP blocks (p,d) = SOME (bbi,_,_,_,_,_,_,_,_,_,_,_,_)`,
       `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,NONE,0,OK s,F,NONE)`] >>
     rpt (pop_assum kall_tac) >> simp[optionTheory.SOME_11,pairTheory.PAIR_EQ] >>
     rpt strip_tac >> gvs[]) >>
  map_every (fn pat => qpat_assum pat SUBST_ALL_TAC) [`sfi = sf`,`orderi = order`,`bbi = bb`] >>
  `order = ds ++ [d]` by
    (qpat_assum `EL 0 orders = order` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT order` by
    (asm "activations" (drule_then (fn th => SUBST1_TAC (cj 6 th))) >>
     simp[NoAsms,ALL_DISTINCT_GENLIST,arithmeticTheory.ADD_CLAUSES]) >>
  `lastcut1 = ds` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LAST order = d`,`ALL_DISTINCT order`,`order = ds ++ [d]`,
        `order = lastcut1 ++ d::later`] >>
     rpt (pop_assum kall_tac) >> disch_then SUBST1_TAC >>
     rpt disch_tac >>
     `later = []` by
       (Cases_on `later` >> fs[ALL_DISTINCT_APPEND,LAST_APPEND] >>
        metis_tac[rich_listTheory.MEM_LAST,listTheory.MEM]) >>
     gvs[APPEND_11]) >>
  qpat_assum `lastcut1 = ds` SUBST_ALL_TAC >>
  qabbrev_tac `rows_pre = MAP (\f. case THE (FLOOKUP blocks (p,f)) of
    (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
      (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds` >>
  `levels = level_pre ++ [(sf,rows_pre ++ [(bb,d,zold)],NONE)]` by
    (qpat_assum `level_pre ++ [LAST levels] = levels` (SUBST1_TAC o SYM) >>
     AP_TERM_TAC >> simp[NoAsms] >>
     qpat_assum `EL (LENGTH cut_pre) levels = _` mp_tac >>
     qpat_assum `SUC (LENGTH cut_pre) = LENGTH cuts` (fn eq => simp[NoAsms,eq]) >>
     qpat_assum `LENGTH cut_pre = LENGTH level_pre` SUBST1_TAC >>
     qpat_assum `level_pre ++ [LAST levels] = levels` (SUBST1_TAC o SYM) >>
     simp[NoAsms,rich_listTheory.EL_LENGTH_APPEND,Abbr `rows_pre`]) >>
  qabbrev_tac `cuts1 = cut_pre ++ [(p,ds,d,q0,z0)]` >>
  qabbrev_tac `levels1 = level_pre ++ [(sf,rows_pre ++ [(bb,d,z0)],NONE)]` >>
  suspend "current_cut_splice"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_splice]:
  `cuts = cut_pre ++ [(p,ds,d,0,zold)]` by
    (qpat_assum `cut_pre ++ [(p,ds,d,0,zold)] = cuts` (ACCEPT_TAC o SYM)) >>
  `MAP (\(ai,ds,ei,qi,zi). ai) cuts1 = MAP (\(ai,ds,ei,qi,zi). ai) cuts` by
    (qpat_assum `cuts = cut_pre ++ [_]` SUBST1_TAC >> simp[NoAsms,Abbr `cuts1`]) >>
  `LENGTH cuts1 = LENGTH cuts /\ LENGTH cuts1 = LENGTH levels1` by
    (qpat_assum `cuts = cut_pre ++ [_]` SUBST1_TAC >>
     qpat_assum `LENGTH cut_pre = LENGTH level_pre` (fn eq =>
       simp[NoAsms,Abbr `cuts1`,Abbr `levels1`,eq])) >>
  `!ai e. FST (THE (FLOOKUP new_blocks (ai,e))) =
          FST (THE (FLOOKUP blocks (ai,e)))` by
    (rpt gen_tac >> Q_TAC ASM_CASES_TAC `(ai,e) = (p,d)`
     >- (qpat_assum `(ai,e) = (p,d)` SUBST1_TAC >>
         asm "current_block_next" (fn th =>
           qpat_assum `FLOOKUP blocks (p,d) = SOME _` (fn old => simp[NoAsms,th,old]))) >>
     asm "off_block" (drule_then SUBST1_TAC) >> REFL_TAC) >>
  suspend "current_cut_tables"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_tables]:
  `!idx. idx < LENGTH cut_pre ==> EL idx cuts1 = EL idx cuts /\
    EL idx levels1 = EL idx levels /\ SUC idx < LENGTH cuts1` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`cuts = cut_pre ++ [_]`,`levels = level_pre ++ [(sf,_,NONE)]`] >>
     qpat_assum `LENGTH cut_pre = LENGTH level_pre` (fn eq =>
       simp[NoAsms,Abbr `cuts1`,Abbr `levels1`,EL_APPEND_EQN,GSYM eq])) >>
  `!idx ai dsi ei qi zi.
    idx < LENGTH cuts1 /\ EL idx cuts1 = (ai,dsi,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP new_blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = dsi ++ ei::later /\
      (if SUC idx = LENGTH cuts1 then ai = p /\ ei = d /\ qi = q0 /\ zi = z0 else
        ?cid ch b0 done_at_call child_entry ret.
          EL (SUC idx) (MAP (\(aj,djs,ej,qj,zj). aj) cuts1) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,ch,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL idx levels1 = (sfi,
        MAP (\f. case THE (FLOOKUP new_blocks (ai,f)) of
          (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
            (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) dsi ++ [(bbi,ei,zi)],
        if SUC idx = LENGTH cuts1 then NONE else SOME (EL qi xsi))` by
    suspend "current_cut_records" >>
  suspend "current_cut_flatten"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_records]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  Q_TAC ASM_CASES_TAC `idx < LENGTH cut_pre`
  >- suspend "current_cut_ancestor_record" >>
  `idx = LENGTH cut_pre` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`idx < LENGTH cuts1`,`~(idx < LENGTH cut_pre)`] >>
     simp[NoAsms,Abbr `cuts1`]) >>
  qpat_assum `idx = LENGTH cut_pre` SUBST_ALL_TAC >>
  `EL (LENGTH cut_pre) cuts1 = (p,ds,d,q0,z0)` by
    simp[NoAsms,Abbr `cuts1`,rich_listTheory.EL_LENGTH_APPEND] >>
  pop_assum (fn eq => qpat_x_assum `EL (LENGTH cut_pre) cuts1 = (ai,dsi,ei,qi,zi)`
    (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) o
      REWRITE_RULE [eq,pairTheory.PAIR_EQ])) >>
  qexistsl [`sf`,`fn`,`inc`,`entry`,`order`,`NONE`,`NONE`,
    `bb`,`bt`,`ps`,`xs`,`ys`,`schedule`,`in_state`,`h0`,
    `if SUC k < LENGTH ps then NONE else SOME (s1,SUC j)`,
    `0`,`OK s1`,`F`,`NONE`,`[]`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- asm "current_block_next" ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `LENGTH cut_pre = LENGTH level_pre` (fn eq =>
    qpat_assum `!ai e. FST (THE (FLOOKUP new_blocks (ai,e))) = _` (fn fst_eq =>
      simp[NoAsms,Abbr `cuts1`,Abbr `levels1`,Abbr `rows_pre`,eq,
        rich_listTheory.EL_LENGTH_APPEND,pairTheory.pair_CASE_def,fst_eq]))
QED

Resume dft_packet_pseudo_next_clauses[current_cut_ancestor_record]:
  qpat_assum `!idx. idx < LENGTH cut_pre ==> _` (drule_then strip_assume_tac) >>
  `idx < LENGTH cuts /\ SUC idx <> LENGTH cuts /\ SUC idx <> LENGTH cuts1` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`LENGTH cuts1 = LENGTH cuts`,`SUC idx < LENGTH cuts1`] >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  qpat_assum `EL idx cuts1 = EL idx cuts` (fn eq =>
    qpat_assum `EL idx cuts1 = (ai,dsi,ei,qi,zi)` (assume_tac o REWRITE_RULE [eq])) >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `SUC idx <> LENGTH cuts` (fn ne =>
    qpat_x_assum `if SUC idx = LENGTH cuts then _ else _`
      (strip_assume_tac o REWRITE_RULE [ne])) >>
  `FLOOKUP new_blocks (ai,ei) = FLOOKUP blocks (ai,ei)` by
    (asm "off_block" irule >>
     asm "call_records" (drule_then strip_assume_tac) >>
     disch_then (fn eq =>
       qpat_assum `FLOOKUP blocks (ai,ei) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`
         (mp_tac o REWRITE_RULE [eq])) >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,NONE,0,OK s,F,NONE)`
       (fn th => simp[NoAsms,th])) >>
  qexistsl [`sfi`,`tfi'`,`inci'`,`enti'`,`orderi`,`resi'`,`nresti'`,
    `bbi`,`bti'`,`psi'`,`xsi'`,`ysi'`,`rhoi'`,`ini'`,`hi'`,`bei'`,`counti'`,
    `fronti'`,`closedi'`,`resti'`,`later'`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_assum `FLOOKUP new_blocks (ai,ei) = _` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `SUC idx <> LENGTH cuts1` (fn ne => simp[NoAsms,ne]) >>
  (conj_tac >- (qpat_assum `MAP _ cuts1 = MAP _ cuts` SUBST1_TAC >>
    goal_assum (drule_at Any) >> rpt conj_tac >> (simp[]))) >>
  qpat_assum `EL idx levels1 = EL idx levels` SUBST1_TAC >>
  qpat_assum `SUC idx <> LENGTH cuts` (fn ne =>
    qpat_assum `EL idx levels = _` (SUBST1_TAC o REWRITE_RULE [ne])) >>
  qpat_assum `!ai e. FST (THE (FLOOKUP new_blocks (ai,e))) = _` (fn eq =>
    simp[NoAsms,pairTheory.pair_CASE_def,eq])
QED

Resume dft_packet_pseudo_next_clauses[current_cut_flatten]:
  qabbrev_tac `Mcut1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms1 (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms1 (ai,ei))))) cuts1)` >>
  qabbrev_tac `Ecut1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es1 (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es1 (ai,ei))))) cuts1)` >>
  qabbrev_tac `Kcut1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks1 (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks1 (ai,ei))))) cuts1)` >>
  qabbrev_tac `mrow = if SUC k < LENGTH ps then [] else cm` >>
  qabbrev_tac `erow = if SUC k < LENGTH ps then [] else ce` >>
  qabbrev_tac `krow = if SUC k < LENGTH ps then [] else ck` >>
  `FST (HD cuts) = []` by
    (qpat_assum `MAP _ cuts = _` (mp_tac o Q.AP_TERM `HD`) >>
     qpat_assum `cuts <> []` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `cuts` >> simp[HD_REVERSE,GENLIST_EQ_NIL,GENLIST_LAST,DROP_LENGTH_TOO_LONG] >>
     rename1 `FST hd` >> PairCases_on `hd` >> simp[]) >>
  `(!i ai dsi ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,dsi,ei,qi,zi) ==>
     ?sfi tfi inci enti orderi resi nresti later.
       FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
       orderi = dsi ++ ei::later /\
       (SUC i < LENGTH cuts ==> ?cid ch b done ent ret.
          FLOOKUP calls (ai,ei,cid) = SOME (qi,ch,b,done,ent,ret) /\
          FST (EL (SUC i) cuts) = (ei,cid)::ai))` by suspend "current_cut_array_geometry" >>
  `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    ALL_DISTINCT order /\ (a = p ==> LAST order = d) /\
    (!i. i < LENGTH p /\ a = DROP (SUC i) p ==> LAST order = FST (EL i p))` by
      suspend "current_cut_array_order" >>
  `FLOOKUP ms1 (p,d) = SOME mrow /\ FLOOKUP es1 (p,d) = SOME erow /\
   FLOOKUP ks1 (p,d) = SOME krow /\ q0 <= LENGTH mrow /\
   LIST_REL (\m e. LENGTH m = LENGTH e) mrow erow /\
   LIST_REL (\m k. LENGTH m = LENGTH k) mrow krow` by suspend "current_cut_array_rows" >>
  suspend "current_cut_array_join"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_geometry]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `FLOOKUP acts ai = SOME (_,_,_,_,_,_,_)` (irule_at Any) >>
  qpat_assum `orderi = dsi ++ ei::later'` (irule_at Any) >>
  disch_tac >> `SUC i <> LENGTH cuts` by simp[] >>
  qpat_assum `SUC i <> LENGTH cuts` (fn ne =>
    qpat_x_assum `if SUC i = LENGTH cuts then _ else _`
      (strip_assume_tac o REWRITE_RULE [ne])) >>
  goal_assum (drule_at Any) >>
  qpat_assum `SUC i < LENGTH cuts` (fn lt =>
    qpat_assum `EL (SUC i) (MAP _ cuts) = _` (mp_tac o REWRITE_RULE [MATCH_MP listTheory.EL_MAP lt])) >>
  simp[NoAsms,pairTheory.ELIM_UNCURRY]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_order]:
  map_every qx_gen_tac [`cut_path0`,`cut_sf0`,`cut_tf0`,`cut_inc0`,`cut_ent0`,
    `cut_order0`,`cut_res0`,`cut_rest0`] >>
  disch_tac >> conj_tac
  >- (asm "activations" (drule_then (fn th => SUBST1_TAC (cj 6 th))) >>
      simp[NoAsms,ALL_DISTINCT_GENLIST,arithmeticTheory.ADD_CLAUSES]) >>
  conj_tac
  >- (disch_then SUBST_ALL_TAC >>
      qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (fn th =>
        qpat_assum `FLOOKUP acts p = SOME (cut_sf0,cut_tf0,cut_inc0,cut_ent0,cut_order0,cut_res0,cut_rest0)`
          (mp_tac o REWRITE_RULE [th,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
      qpat_assum `LAST order = d` mp_tac >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  qx_gen_tac `cut_idx0` >> strip_tac >>
  qsuff_tac `?pf pt pi pe po.
     FLOOKUP acts (DROP (SUC cut_idx0) p) = SOME (pf,pt,pi,pe,po,NONE,NONE) /\
     LAST po = FST (EL cut_idx0 p)`
  >- (qpat_assum `FLOOKUP acts cut_path0 = SOME _` mp_tac >>
      qpat_assum `cut_path0 = DROP (SUC cut_idx0) p` mp_tac >>
      rpt (pop_assum kall_tac) >>
      metis_tac[optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
  asm "parents" (qspec_then `cut_idx0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  rpt (pop_assum kall_tac) >> metis_tac[pairTheory.FST]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_rows]:
  asm "block_records" (drule_then strip_assume_tac) >>
  qpat_assum `(case (NONE:(venom_state # num) option) of NONE => _ | SOME _ => _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.option_case_def]) >>
  Cases_on `SUC k < LENGTH ps` >- suspend "current_cut_array_interior" >>
  suspend "current_cut_array_boundary"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_interior]:
  `q0 = 0` by
    (qpat_assum `IS_SOME (if SUC k < LENGTH ps then NONE else SOME _) /\ _ \/ _` mp_tac >>
     qpat_assum `SUC k < LENGTH ps` (fn th => simp[NoAsms,th])) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`Abbrev (mrow = _)`,`Abbrev (erow = _)`,`Abbrev (krow = _)`,
     `Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`,
     `FLOOKUP ms_tab (p,d) = SOME []`,`FLOOKUP es_tab (p,d) = SOME []`,
     `FLOOKUP ks_tab (p,d) = SOME []`,`q0 = 0`,`SUC k < LENGTH ps`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  simp[Abbr `mrow`,Abbr `erow`,Abbr `krow`,Abbr `ms1`,Abbr `es1`,Abbr `ks1`]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_boundary]:
  `q0 < LENGTH xs` by
    (qpat_assum `IS_SOME (if SUC k < LENGTH ps then NONE else SOME _) /\ _ \/ _` mp_tac >>
     qpat_assum `~(SUC k < LENGTH ps)` (fn th => simp[NoAsms,th]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`Abbrev (mrow = _)`,`Abbrev (erow = _)`,`Abbrev (krow = _)`,
     `Abbrev (cm = _)`,`Abbrev (ce = _)`,`Abbrev (ck = _)`,
     `FLOOKUP ms_new (p,d) = SOME cm`,`FLOOKUP es_new (p,d) = SOME ce`,
     `FLOOKUP ks_new (p,d) = SOME ck`,
     `Abbrev (ms1 = _)`,`Abbrev (es1 = _)`,`Abbrev (ks1 = _)`,
     `q0 < LENGTH xs`,`~(SUC k < LENGTH ps)`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  simp[Abbr `mrow`,Abbr `erow`,Abbr `krow`,Abbr `ms1`,Abbr `es1`,Abbr `ks1`,
       Abbr `cm`,Abbr `ce`,Abbr `ck`,LIST_REL_EL_EQN,EL_GENLIST] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_join]:
  `Mcut1 = Mcut ++ FLAT (TAKE q0 mrow) /\ (?rest. AM1 [] = Mcut1 ++ rest) /\
   Ecut1 = Ecut ++ FLAT (TAKE q0 erow) /\ (?rest. AE1 [] = Ecut1 ++ rest) /\
   Kcut1 = Kcut ++ FLAT (TAKE q0 krow) /\ (?rest. AK1 [] = Kcut1 ++ rest) /\
   LENGTH Mcut1 = LENGTH Ecut1 /\ LENGTH Mcut1 = LENGTH Kcut1` by
    suspend "current_cut_array_apply" >>
  qmatch_asmsub_rename_tac `AM1 [] = Mcut1 ++ mr1` >>
  qmatch_asmsub_rename_tac `AE1 [] = Ecut1 ++ er1` >>
  qmatch_asmsub_rename_tac `AK1 [] = Kcut1 ++ kr1` >>
  qexistsl [`cuts1`,`levels1`,`Mcut1`,`Ecut1`,`Kcut1`,`mr1`,`er1`,`kr1`] >>
  conj_tac >- (qpat_assum `MAP _ cuts1 = MAP _ cuts` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every (fn x => conj_tac >- simp[NoAsms,Abbr x]) [`Mcut1`,`Ecut1`,`Kcut1`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "current_cut_eval"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_array_apply]:
  pure_rewrite_tac[GSYM CONJ_ASSOC] >>
  MATCH_MP_TAC (PURE_REWRITE_RULE [GSYM CONJ_ASSOC]
    dft_packet_pseudo_current_cut_arrays) >>
  qpat_assum `cuts = cut_pre ++ [(p,ds,d,0,zold)]` (irule_at Any) >>
  qpat_assum `Abbrev (cuts1 = _)`
    (irule_at Any o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qexistsl [`ms1`,`ms_tab`,`ks1`,`ks_tab`,`es1`,`es_tab`,`calls`,`acts`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
    map_every (fn label => asm label (drule_all_then assume_tac o cj 1))
      ["mask_history","site_history","key_history"] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- (rpt gen_tac >> disch_tac >>
    map_every (fn label => asm label (fn th =>
      drule_then (assume_tac o CONJUNCT1) (cj 3 th) >>
      drule_then assume_tac (cj 8 th)))
      ["mask_history","site_history","key_history"] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every (fn ab => conj_tac >- simp[NoAsms,Abbr ab])
    [`AM1`,`AE1`,`AK1`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every (fn ab => conj_tac >- simp[NoAsms,Abbr ab])
    [`Mcut1`,`Ecut1`,`Kcut1`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_next_clauses[current_cut_eval]:
  `MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
    (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts1 =
   MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
    (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts` by
    (qpat_assum `cuts = cut_pre ++ [_]` SUBST1_TAC >> simp[NoAsms,Abbr `cuts1`]) >>
  `!fuel gs tail. N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut1 gs ==>
    levels_ok fuel C7 levels1 (MAP (\(ai,ds,ei,qi,zi). ai) cuts1)
      (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
        (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts1)
      root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. Ecut1 = FST (rooted_eval fuel C7 levels1
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval fuel C7 levels1 (root_entry with vs_gas_readings := gs ++ tail)) of
      OK v => FST (rooted_eval fuel C7 levels1 (root_entry with vs_gas_readings := gs ++ tail)) = Ecut1 /\
        v.vs_gas_readings = tail /\
        (?before after. trace_blocks [] 0 fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          before ++ [((p,d,(EL (LENGTH z0) (DROP l bb.bb_instructions)).inst_id),sf,
            EL (LENGTH z0) (DROP l bb.bb_instructions),v)] ++ after /\
          trace_gas before = ZIP (Kcut1,gs)) /\
        (!tail'. rooted_eval fuel C7 levels1 (root_entry with vs_gas_readings := gs ++ tail') =
          (Ecut1,OK (v with vs_gas_readings := tail'))) /\
        (SUC k < LENGTH ps ==> v with vs_gas_readings := s1.vs_gas_readings = s1)
    | stopped => run_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval fuel C7 levels1 (root_entry with vs_gas_readings := gs ++ tail)))` by
    suspend "current_cut_fresh_apply" >>
  suspend "current_cut_replay_join"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_fresh_apply]:
  map_every (fn pat => qpat_assum pat SUBST1_TAC)
    [`Mcut1 = Mcut ++ FLAT (TAKE q0 mrow)`,
     `Ecut1 = Ecut ++ FLAT (TAKE q0 erow)`,
     `Kcut1 = Kcut ++ FLAT (TAKE q0 krow)`] >>
  MATCH_MP_TAC (GEN_ALL (cj 3 dft_packet_pseudo_fresh_cut)) >>
  suspend "current_cut_fresh_inputs"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_fresh_inputs]:
  qexistsl [`zold`,`xs`,`u`,`s`,`rows_pre`,`row_eval`,`q0`,`plan_ok`,`plan_eval`,
    `MAP (\(ai,ds,ei,qi,zi). ai) cuts`,`cm`,`levels`,`level_pre`,`ck`,
    `N-d`,`ce`,`ds`,`cuts`,`cut_pre`,`call_setup`,`C8`] >>
  ntac 6 (asm_x "evaluators" assume_tac) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (sym_tac >> first_assum ACCEPT_TAC)) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`lookup_block s.vs_current_bb fn.fn_blocks = SOME bt`,
       `lookup_block bb.bb_label sf.fn_blocks = SOME bb`,`bt.bb_label = bb.bb_label`] >>
     rpt (pop_assum kall_tac) >> metis_tac[venomExecPropsTheory.lookup_block_label])) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_assum `phi_prefix_length bb.bb_instructions = l` (fn eq =>
     qpat_assum `s.vs_inst_idx = k` (fn idx => simp[NoAsms,Abbr `zold`,eq,idx])))) >>
  map_every (fn ab => conj_tac >- simp[NoAsms,Abbr ab]) [`cm`,`ce`,`ck`] >>
  (conj_tac >- suspend "current_cut_phase_inputs") >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- simp[NoAsms,Abbr `cuts1`]) >>
  (conj_tac >- REFL_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- simp[NoAsms,Abbr `levels1`]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
    (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts1 = _` SUBST1_TAC >>
  qpat_assum `phi_prefix_length bb.bb_instructions = l` (SUBST1_TAC o SYM) >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==>
    levels_ok F C7 levels _ _ _ _ [] 0 /\ _` mp_tac >>
  simp[NoAsms]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_phase_inputs]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`IS_SOME (if SUC k < LENGTH ps then NONE else SOME _) /\ _ \/ _`,
     `s1 = u with vs_inst_idx := SUC k`,`k < LENGTH ps`,
     `phi_prefix_length bb.bb_instructions = l`,
     `Abbrev (mrow = _)`,`Abbrev (erow = _)`,`Abbrev (krow = _)`] >>
  rpt (pop_assum kall_tac) >> rpt (disch_then assume_tac) >>
  Cases_on `SUC k < LENGTH ps` >>
  gvs[Abbr `mrow`,Abbr `erow`,Abbr `krow`] >> metis_tac[]
QED

Resume dft_packet_pseudo_next_clauses[current_cut_replay_join]:
  qx_gen_tac `fuel` >> qx_gen_tac `gs` >> qx_gen_tac `tail` >> strip_tac >>
  qpat_assum `!fuel gs tail. N <= fuel /\ LIST_REL _ Mcut1 gs ==> _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  `sf0 = sf` by
    (qpat_assum `FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE)` (fn th =>
       qpat_assum `FLOOKUP acts p = SOME (sf0,_,_,_,_,_,_)`
         (mp_tac o REWRITE_RULE [th])) >>
     simp[NoAsms,pairTheory.PAIR_EQ]) >>
  map_every (fn pat => qpat_assum pat SUBST1_TAC)
    [`sf0 = sf`,`phi_prefix_length bb.bb_instructions = l`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (mk_asm "fresh_semantics"))) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  Cases_on `rooted_eval fuel C7 levels1 (root_entry with vs_gas_readings := gs ++ tail)` >>
  rename1 `rooted_eval fuel C7 levels1 _ = (events,result)` >>
  Cases_on `result` >>
  asm_x "fresh_semantics" mp_tac >>
  simp[NoAsms] >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  Cases_on `SUC k < LENGTH ps`
  >- (qpat_assum `SUC k < LENGTH ps` (fn th => simp[NoAsms,th])) >>
  qpat_assum `~(SUC k < LENGTH ps)` (fn th => simp[NoAsms,th]) >>
  strip_tac >> suspend "current_cut_observation"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_observation]:
  `SUC k = LENGTH ps` by
    (qpat_assum `~(SUC k < LENGTH ps) ==> SUC k = LENGTH ps` drule >> simp[]) >>
  qpat_assum `SUC k = LENGTH ps ==> dft_remaining_inv sf bb xs s1` drule >> strip_tac >>
  qpat_assum `SUC k = LENGTH ps ==> ys <> [] /\ _` drule >> strip_tac >>
  `Mcut1 = Mcut ++ FLAT (TAKE q0 cm)` by
    (qpat_assum `Mcut1 = Mcut ++ FLAT (TAKE q0 mrow)` SUBST1_TAC >>
     qpat_assum `~(SUC k < LENGTH ps)` (fn th => simp[NoAsms,Abbr `mrow`,th])) >>
  `?gs0 gs1. gs = gs0 ++ gs1 /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs0 /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q0 cm)) gs1` by
    (qpat_assum `LIST_REL _ Mcut1 gs` mp_tac >>
     qpat_assum `Mcut1 = Mcut ++ FLAT (TAKE q0 cm)` SUBST1_TAC >>
     simp[NoAsms,LIST_REL_SPLIT1]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `LIST_REL _ (FLAT (TAKE q0 cm)) gs1`
    (mp_then (Pat `LIST_REL _ (FLAT _) _`) strip_assume_tac
       dftPacketFillingBoundaryTheory.dft_packet_flat_filling_split) >>
  rename1 `gs1 = FLAT kgss` >>
  `!ev w. rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
      (ev,OK w) ==> w = s with vs_gas_readings := FLAT kgss ++ tail` by
    suspend "current_cut_old_endpoint" >>
  suspend "current_cut_observation_apply"
QED

Resume dft_packet_pseudo_next_clauses[current_cut_old_endpoint]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`
    (qspecl_then [`fuel`,`gs0`,`gs1 ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `gs = gs0 ++ gs1` (fn th =>
    qpat_assum `rooted_eval fuel C7 levels _ = (ev,OK w)`
      (fn eq => simp[NoAsms,REWRITE_RULE [th,GSYM APPEND_ASSOC] eq])) >>
  strip_tac >>
  qpat_assum `w with vs_gas_readings := s.vs_gas_readings = s` (fn th =>
    GEN_REWRITE_TAC (RHS_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM th]) >>
  qpat_assum `w.vs_gas_readings = gs1 ++ tail` (fn th =>
    qpat_assum `gs1 = FLAT kgss` (fn eq => simp[NoAsms,GSYM eq,GSYM th]))
QED

Resume dft_packet_pseudo_next_clauses[current_cut_observation_apply]:
  `bb_well_formed bt` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`dft_fn_rel sf fn`,`fn = dft_fn sf`,
       `lookup_block bb.bb_label fn.fn_blocks = SOME bt`] >>
     rpt (pop_assum kall_tac) >> simp[dft_fn_rel_def] >>
     metis_tac[dftCorrectnessTheory.dft_fn_blocks_well_formed,
               venomExecPropsTheory.lookup_block_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (qpat_assum `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` mp_tac >>
     qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
     simp[NoAsms,ALL_DISTINCT_APPEND]) >>
  `q0 < LENGTH xs /\ z0 = DROP l ps ++ TAKE q0 xs /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q0 xs)` by
    suspend "current_cut_observation_prefix" >>
  `EL q0 xs = HD ys` by
    (qpat_assum `i1 = HD ys` (fn eq => simp[NoAsms,GSYM eq]) >>
     first_assum ACCEPT_TAC) >>
  `inv_memory_observation (EL q0 xs).inst_opcode` by
    (qpat_assum `EL q0 xs = i1` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `l = phi_prefix_length bb.bb_instructions` by
    (sym_tac >> first_assum ACCEPT_TAC) >>
  `zold = DROP l (TAKE k ps)` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC)
      [`l = phi_prefix_length bb.bb_instructions`, `k = s.vs_inst_idx`] >>
     simp[NoAsms,Abbr `zold`]) >>
  qpat_assum `Abbrev (levels1 = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (cm = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  ntac 6 (asm_x "evaluators" assume_tac) >>
  map_every (fn pat => qpat_assum pat
    (fn th => assume_tac (BETA_RULE (Q.AP_THM (Q.AP_THM th `fuel`) `C7`))))
    [`row_eval = _`, `plan_eval = _`, `rooted_eval = _`] >>
  qpat_assum `call_setup = _`
    (fn th => assume_tac (BETA_RULE (Q.AP_THM th `C7`))) >>
  qpat_assum `EL q0 xs = i1` (SUBST1_TAC o SYM) >>
  let
    fun apply [] th = ACCEPT_TAC (CONJUNCT2 th)
      | apply (pat::pats) th = qpat_assum pat (mp_then (Pos hd) (apply pats) th)
  in
    apply
      [`row_eval fuel C7 = _`, `plan_eval fuel C7 = _`, `call_setup C7 = _`,
       `rooted_eval fuel C7 = _`, `LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions`,
       `dft_fn_rel sf fn`, `MEM bb sf.fn_blocks`,
       `lookup_block bb.bb_label sf.fn_blocks = SOME bb`,
       `lookup_block bb.bb_label fn.fn_blocks = SOME bt`,
       `bb.bb_instructions = ps ++ xs`, `bt.bb_instructions = ps ++ ys`,
       `EVERY (\i. is_pseudo i.inst_opcode) ps`,
       `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,
       `EVERY inst_shape_ok bb.bb_instructions`, `bb_well_formed bt`,
       `ALL_DISTINCT (MAP (\i. i.inst_id) xs)`, `l = phi_prefix_length bb.bb_instructions`,
       `l <= k`, `k < LENGTH ps`, `SUC k = LENGTH ps`, `s.vs_inst_idx = k`,
       `step_inst (N-d) C8 (EL k ps) s = OK u`, `s1 = u with vs_inst_idx := SUC k`,
       `dft_remaining_inv sf bb xs s1`, `q0 < LENGTH xs`, `ys <> []`,
       `EL q0 xs = HD ys`, `inv_memory_observation (EL q0 xs).inst_opcode`,
       `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q0 xs)`,
       `cm = GENLIST _ _`, `LIST_REL _ (TAKE q0 cm) kgss`,
       `zold = DROP l (TAKE k ps)`, `z0 = DROP l ps ++ TAKE q0 xs`,
       `levels = level_pre ++ [(sf,rows_pre ++ [(bb,d,zold)],NONE)]`,
       `levels1 = level_pre ++ [(sf,rows_pre ++ [(bb,d,z0)],NONE)]`,
       `!ev w. rooted_eval fuel C7 levels _ = (ev,OK w) ==> w = s with vs_gas_readings := _`,
       `rooted_eval fuel C7 levels1 _ = (events,OK v)`]
      (Q.SPEC `fuel` dft_packet_first_body_rooted_observation)
  end
QED

Resume dft_packet_pseudo_next_clauses[current_cut_observation_prefix]:
  qpat_assum `IS_SOME (if SUC k < LENGTH ps then NONE else SOME _) /\ _ \/ _` mp_tac >>
  qpat_assum `~(SUC k < LENGTH ps)` (fn th =>
    qpat_assum `phi_prefix_length bb.bb_instructions = l` (fn eq => simp[NoAsms,th,eq])) >>
  strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms,EVERY_CONJ] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms,EVERY_EL] >> qx_gen_tac `r` >> strip_tac >>
  `r < q0` by
    (qpat_assum `r < LENGTH (TAKE q0 xs)` mp_tac >> simp[NoAsms,LENGTH_TAKE_EQ]) >>
  qpat_assum `!r. (EL r xs).inst_opcode = INVOKE ==> ~(r < q0)`
    (qspec_then `r` mp_tac) >>
  qpat_assum `r < q0` (fn th => simp[NoAsms,th,EL_TAKE])
QED

Finalise dft_packet_pseudo_next_clauses
