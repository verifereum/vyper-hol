Theory dftPacketReturnParentCutApplication
Ancestors
  dftPacketReturnNewCuts venomExecProofs

Theorem return_cut_pair_projection[local]:
  pair_CASE x f = f (FST x) (SND x)
Proof
  Cases_on `x` >> simp[]
QED

(* Obtain the parent anchor from the old rooted-cut clause, before fixing fuel
   or readings. The return does not change any of the three row-array maps. *)
Theorem dft_packet_return_parent_cut_application:
  !(N:num) C7 C8 root_sf root_tf root_entry
    (acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    row_eval plan_eval call_setup rooted_eval plan_ok levels_ok cp rho.
  row_eval = (\F C owner (bb,e,z) s.
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
       else call = NONE))) /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  (?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!e. MEM e order <=> (a,e) IN FDOM blocks)) /\
  (!a e bb bt ps xs ys rho hin h0 body count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      MEM e order /\ bb.bb_instructions = ps ++ xs /\
      bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      eval_phis hin bt.bb_instructions = OK sp /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (a,e-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      (closed <=> IS_SOME brest) /\
      (case body of NONE => a = p /\ e = d
       | SOME (be,hbe) =>
           FOLDR (dft_exec_cons (N-e) C8) OK
             (DROP (phi_prefix_length bt.bb_instructions) ps)
             (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be) /\
      (e <> LAST order ==> closed)) /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\
  FDOM blocks = FDOM ks_tab /\
  (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
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
      (!F k kgss tail.
        N <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
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
            (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'.
            FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))))) /\
  (!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count r8 u0 ms ess ks.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
    !F. N <= F ==> !gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
      (?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
        (be with vs_gas_readings := gs ++ tail))) ==>
      (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
        residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
          (be with vs_gas_readings := gs ++ tail)))) /\
  (!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count front closed brest
      csf ctf child_order child_res child_rest nm ops args.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      done = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done /\
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE count rho))) /\
  (!k. k < LENGTH p ==>
    ?bb' bt' ps' xs' ys' rho' hin' h0' be' hbe' cnt'
      q' h' b0' done' child_entry' cid' e' a'.
      a' = DROP (SUC k) p /\ (e',cid') = EL k p /\
      FLOOKUP blocks (a',e') =
        SOME (bb',bt',ps',xs',ys',rho',hin',h0',SOME (be',hbe'),cnt',OK b0',F,NONE) /\
      FLOOKUP calls (a',e',cid') = SOME (q',h',b0',done',child_entry',NONE) /\
      done' = TAKE cnt' rho') /\
  (!a e cid q h b0 done child_entry ret bb bt ps xs ys rho hin h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee argv. setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee argv b0)) /\
  p = (e,cid)::a /\
  FLOOKUP acts p = SOME (csf,ctf,e,child_entry,child_order,NONE,NONE) /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (cb,ct,cp,cx,cy,cr,ci,ch,SOME (cbe,chbe),cc,OK st,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),cnt,OK b0,F,NONE) /\
  FLOOKUP calls (a,e,cid) = SOME (cq,call_h,b0,done,child_entry,NONE) /\
  acts' = acts |+ (p,(csf,ctf,e,child_entry,child_order,
    SOME (IntRet ir child_out),SOME child_out.vs_gas_readings)) /\
  blocks' = blocks |+
    ((p,d),(cb,ct,cp,cx,cy,cr,ci,ch,SOME (cbe,chbe),
      LENGTH cy,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
    ((a,e),(bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),SUC cnt,
      OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((a,e,cid),
    (cq,call_h,b0,done,child_entry,SOME (ir,child_out,caller_post))) /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  (!a e q z sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    ((IS_SOME body_entry /\ q < LENGTH xs /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
      (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==>
        MEM r (TAKE count rho))) \/
     (body_entry = NONE /\ a = p /\ e = d /\ q = 0 /\
      z = DROP (phi_prefix_length bb.bb_instructions) (TAKE st.vs_inst_idx ps))) ==>
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
          (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z
           else ?cid h b0 done_at_call child_entry ret.
             EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
             FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
             qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
             zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
             EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
             (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
          EL i levels =
            (sfi, MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
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
        N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
        levels_ok F C7 levels
          (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
          (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
            (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
          root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
        (?extra. Ecut = FST (rooted_eval F C7 levels
          (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
        (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
          OK u =>
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
            u.vs_gas_readings = tail /\
            (?before after.
              trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
                before ++ [((a,e,(EL (LENGTH z)
                  (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
              trace_gas before = ZIP (Kcut,gs)) /\
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
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\
  FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  be.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE (SUC cnt) rho)) /\
  (!F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE (SUC cnt) rho)) /\
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
        (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
      (!tail'.
        FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs ==>
  ?cuts levels Mcut Ecut Kcut mr er kr.
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
        (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z
         else ?cid h b0 done child_entry ret.
           EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
           FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
           qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
           zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
           EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
           (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
        EL i levels =
          (sfi,MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
            DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
              (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
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
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      levels_ok F C7 levels
        (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
        (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail')))
      | stopped =>
          run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!a e q z sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 body count front closed brest. _`
    (qspecl_then [`a`,`e`,`0`,`DROP (phi_prefix_length bb.bb_instructions) ps`] mp_tac) >>
  disch_then (drule_at_then (Pos (hd o tl)) (drule_then mp_tac)) >>
  impl_tac >- (simp[] >> decide_tac) >>
  disch_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [return_cut_pair_projection]) >>
  `(!aa ee ci qi hh s ds ent ret.
     FLOOKUP calls (aa,ee,ci) = SOME (qi,hh,s,ds,ent,ret) ==>
     ?mm ss kk. FLOOKUP ms_tab (aa,ee) = SOME mm /\
       FLOOKUP es_tab (aa,ee) = SOME ss /\ FLOOKUP ks_tab (aa,ee) = SOME kk /\
       qi < LENGTH mm /\ qi < LENGTH ss /\ qi < LENGTH kk /\
       EL qi mm = AM ((ee,ci)::aa) /\ EL qi ss = AE ((ee,ci)::aa) /\
       EL qi kk = AK ((ee,ci)::aa))` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a e cid q h s ds ent ret. FLOOKUP calls _ = SOME _ ==> _`
       (drule_then strip_assume_tac) >>
     `?mm. FLOOKUP ms_tab (aa,ee) = SOME mm` by metis_tac[FDOM_FLOOKUP] >>
     `?ss. FLOOKUP es_tab (aa,ee) = SOME ss` by metis_tac[FDOM_FLOOKUP] >>
     `?kk. FLOOKUP ks_tab (aa,ee) = SOME kk` by metis_tac[FDOM_FLOOKUP] >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
                   FLOOKUP blocks _ = SOME _ /\ _ ==> _`
       (fn th => qpat_assum `FLOOKUP blocks (aa,ee) = SOME _`
         (mp_then (Pos hd) (drule_all_then strip_assume_tac) th)) >>
     first_x_assum (drule_then (qspec_then `qi` mp_tac o CONJUNCT1)) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_tac o cj 3) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (fn th => qexistsl [`mm`,`ss`,`kk`] >> mp_tac th) >>
     FILTER_ASM_REWRITE_TAC (fn t =>
       can (match_term ``FLOOKUP calls _ = SOME _``) t orelse
       can (match_term ``(EL q xs).inst_id = _``) t) [] >>
     simp[NoAsms] >>
     disch_tac >> simp[]) >>
  irule dft_packet_return_parent_new_cuts >>
  conj_tac >- (rpt (goal_assum $ drule_at Any) >> simp[]) >>
  (* Match the concrete updates first. Their tuple fields determine the
     resumed row and the completed child simultaneously. *)
  qpat_assum `blocks' = _` (fn th =>
    part_match_exists_tac (find_term (can (match_term ``x = y |+ _ |+ _``))) (concl th)) >>
  qpat_assum `acts' = _` (fn th =>
    part_match_exists_tac (find_term (can (match_term ``x = y |+ (_,(_,_,_,_,_,SOME (IntRet _ _),_))``)))
      (concl th)) >>
  qpat_assum `calls' = _` (fn th =>
    part_match_exists_tac (find_term (can (match_term ``x = y |+ (_,(_,_,_,_,_,SOME (_,_,_)))``)))
      (concl th)) >>
  (* Lookup keys fix the remaining row and activation fields. Also fix the
     anchor arrays by matching their retained-table expressions. *)
  map_every (fn pat => qpat_assum pat (fn th =>
    part_match_exists_tac (fn b => List.find (fn c => is_eq c andalso
      aconv (lhs c) (lhs (concl th))) (strip_conj b) |> valOf) (concl th)))
    [`FLOOKUP blocks (p,d) = SOME _`, `FLOOKUP acts a = SOME _`,
     `FLOOKUP ms_tab (a,e) = SOME _`, `FLOOKUP es_tab (a,e) = SOME _`,
     `FLOOKUP ks_tab (a,e) = SOME _`] >>
  qpat_assum `LIST_REL dft_fn_rel _ _` (fn th =>
    part_match_exists_tac (find_term (can (match_term ``LIST_REL dft_fn_rel _ _``))) (concl th)) >>
  qpat_assum `?ord. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,ord,NONE,NONE)` (fn th =>
    part_match_exists_tac (valOf o List.find is_exists o strip_conj) (concl th)) >>
  qpat_assum `MAP _ cuts = REVERSE _` (fn th =>
    part_match_exists_tac (find_term (can (match_term ``MAP _ _ = REVERSE _``))) (concl th)) >>
  qpat_assum `LENGTH cuts = LENGTH levels` (fn th =>
    part_match_exists_tac (fn b => List.find (fn c => is_eq c andalso
      aconv (lhs c) (lhs (concl th))) (strip_conj b) |> valOf) (concl th)) >>
  map_every (fn pat => qpat_assum pat (fn th =>
    part_match_exists_tac (fn b => List.find (fn c => is_eq c andalso
      aconv (rhs c) (rhs (concl th))) (strip_conj b) |> valOf) (concl th)))
    [`Mcut = _`, `Ecut = _`, `Kcut = _`] >>
  qexists `DROP (phi_prefix_length bb.bb_instructions) ps` >>
  rpt conj_tac >> rpt (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >>
      disch_then (fn lookups =>
        qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
                     FLOOKUP blocks _ = SOME _ /\ _ ==> _`
          (mp_tac o C MATCH_MP lookups)) >>
      disch_then (fn row =>
        conj_tac >- ACCEPT_TAC (CONJUNCT1 row) >>
        rpt gen_tac >> disch_tac >>
        drule_then (ACCEPT_TAC o CONJUNCT2) (List.last (CONJUNCTS row))))
  >- (map_every qx_gen_tac [`F0`,`gs0`,`tail0`] >>
      disch_then (fn guard =>
        qpat_assum `!F gs tail. _ ==> levels_ok _ _ levels _ _ _ _ _ _ /\ _`
          (qspecl_then [`F0`,`gs0`,`tail0`] (mp_tac o C MP guard))) >>
      Cases_on `SND (rooted_eval F0 C7 levels
        (root_entry with vs_gas_readings := gs0 ++ tail0))` >>
      simp[NoAsms] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- REFL_TAC >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
               FLOOKUP blocks _ = SOME _ /\ _ ==> _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (mp_then (Pos hd) (drule_all_then
        (fn row => map_every assume_tac (List.take (CONJUNCTS row,5)))) th)) >>
  first_assum ACCEPT_TAC
QED
