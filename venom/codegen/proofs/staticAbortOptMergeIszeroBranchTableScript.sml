Theory staticAbortOptMergeIszeroBranchTable
Ancestors
  staticAbortOptMergeIszeroLayout staticAbortOptMergeIszeroLive
  staticAbortStraight
  asmSplice asmSymPc asmSymBridge asmSymSem asmDataEnv stackOpSim stackOpAsmSim
  alist finite_map pred_set list rich_list arithmetic words
  staticAbortOptMergeIszeroBranchSelector staticAbortOptMergeIszeroBranchControl
  staticAbortOptMergeIszeroBranchDispatch staticAbortOptMergeIszeroBranchFlow
  staticAbortOptMergeIszeroBranchSlots staticAbortOptMergeIszeroBranchActualRoot

(* The two tests are the only erased PCs. In particular the fall from
   immediately before the window enters the relocated push. *)
Triviality branch_relinked_fall:
  !keep. keep = (\k:num. k < b \/ b+2 <= k) ==>
  !f. f = (\k:num. if k < b then k else k-2) ==>
  keep i /\ (if keep (i+1) then j=i+1 else j=b+2) ==>
  f j = f i+1
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "next")) >>
  Cases_on `i < b`
  >- (Cases_on `i+1 < b`
      >- (asm_x "next" mp_tac >> simp[]) >>
      `i+1 = b` by decide_tac >>
      `~(b+2 <= i+1)` by decide_tac >>
      `~(b+2 < b)` by decide_tac >>
      asm_x "next" mp_tac >> simp[] >> decide_tac) >>
  `b+2 <= i` by decide_tac >>
  `b+2 <= i+1 /\ ~(i+1 < b)` by decide_tac >>
  asm_x "next" mp_tac >> simp[] >> decide_tac
QED

Triviality branch_test_suffix:
  !pre l tail b p i.
  b = LENGTH pre /\
  p = pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail /\
  (i=b \/ i=b+1) ==>
  asm_block_at p i (REPLICATE (b+2-i) (AsmOp "ISZERO"))
Proof
  rpt strip_tac >>
  simp[EVAL ``REPLICATE 1 (AsmOp "ISZERO")``,
       EVAL ``REPLICATE 2 (AsmOp "ISZERO")``, asm_block_at_cons,
       EL_APPEND_EQN, rich_listTheory.EL_CONS, GSYM arithmeticTheory.ADD_ASSOC]
QED

Triviality branch_path_last:
  (?n (path:num->num#num).
     path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) ==>
  x=e \/ ?y. edge y x
Proof
  strip_tac >> Cases_on `n` >- gvs[] >>
  disj2_tac >> qexists_tac `path n'` >>
  gvs[]
QED

(* The workers spell out the same lexical packet in different orders.
   Normalize only the selected bindings, using exact matching for the join. *)
val branch_unwind = HO_REWR_CONV UNWIND_FORALL_THM2
fun branch_unwind_group tm =
  case strip_forall tm of
    (v::_::_, body) =>
      if is_imp body andalso is_eq (lhand body) andalso aconv (lhs (lhand body)) v
      then CHANGED_CONV Unwind.UNWIND_FORALL_CONV tm else NO_CONV tm
  | _ => NO_CONV tm
val branch_norm = REDEPTH_CONV
  (BETA_CONV ORELSEC branch_unwind ORELSEC branch_unwind_group)

fun branch_intro name = qx_gen_tac name >> disch_then (assume_tac o
  CONV_RULE (RAND_CONV branch_norm THENC REWR_CONV (GSYM markerTheory.Abbrev_def)))

fun branch_with names ttac = ASSUM_LIST (fn asms =>
  let
    fun binding th =
      let val eq = REWRITE_RULE [markerTheory.Abbrev_def] th
          val name = fst (dest_var (lhs (concl eq)))
      in if List.exists (fn n => n = name) names then SOME eq else NONE end
      handle HOL_ERR _ => NONE
    val rules = List.mapPartial (fn th =>
      if can (find_term (same_const ``marker$Abbrev``)) (concl th)
      then binding th else NONE) asms
  in ttac (PURE_REWRITE_CONV rules THENC branch_norm) end)

fun branch_exact names = branch_with names (fn cv =>
  first_assum (ACCEPT_TAC o CONV_RULE cv))

fun branch_worker names th prove_inputs =
  branch_with names (fn cv => CONV_TAC cv) >>
  mp_tac (CONV_RULE branch_norm th) >> (impl_tac >- prove_inputs) >>
  disch_then ACCEPT_TAC

(* Instantiate ordinary arguments first, then discharge lexical equalities. *)
fun branch_shared args binds worker use = ASSUM_LIST (fn asms =>
  goal_term (fn goal =>
    let
      val vars = List.concat (map free_vars (goal :: map concl asms))
      fun live name ty =
        case List.find (fn tm => dest_var tm = (name,ty)) vars of
          SOME tm => tm
        | NONE => raise Fail ("no live " ^ name ^ " : " ^ type_to_string ty)
      fun arg (name,th) =
        SPEC (live name (type_of (fst (dest_forall (concl th))))) th
      fun bind (NONE,th) = CONV_RULE branch_unwind th
        | bind (SOME name,th) =
            let
              val step = CONV_RULE (LAND_CONV branch_norm) (arg (name,th))
              val eq = fst (dest_imp (concl step))
              val marked = REWR_CONV markerTheory.Abbrev_def THENC branch_norm
              val facts = List.mapPartial (fn a =>
                SOME (CONV_RULE marked a) handle HOL_ERR _ => NONE) asms
            in
              case List.find (fn a => aconv (concl a) eq) facts of
                SOME a => MP step a
              | NONE => raise Fail ("unmatched shared binding: " ^ name)
            end
    in use (List.foldl bind (List.foldl arg worker args) binds) end))

Theorem merge_iszero_jumpi_cut_table:
  !b. b = LENGTH pre ==>
  !c. c = ss.sym_base.as_pc ==>
  !Shape. Shape =
    (\p cc req pc height need tag boolean i (s:asm_state).
      s.as_pc = pc i /\ LENGTH s.as_stack = height i /\
      s.as_call_ctx = cc /\ s.as_requests = req /\
      (need i ==> s.as_call_ctx.cc_static) /\
      (!k l origin. tag i k = SOME(l,origin) ==>
         k < height i /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
         ?off dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k s.as_stack = (n2w off:bytes32)) /\
      (!k. boolean i k ==> k < height i /\
         (EL k s.as_stack = 0w \/ EL k s.as_stack = 1w))) ==>
  !Flow. Flow =
    (\p pc height tag boolean (x:num#num) (y:num#num).
      !hi. hi = height x ==> !hj. hj = height y ==> !ins. ins = EL (pc x) p ==>
      !inherit. inherit = (\(src:num->num option) (fresh:num->(string#num)option) (bnew:num->bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
           ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
      case ins of
        AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
      | AsmPush bs => hj = hi+1 /\
          inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
            (\k. k=0 /\ !s u.
              asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
                (AsmPush bs) s = AsmOK u ==> (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
      | AsmPushLabel l => hj = hi+1 /\
          inherit (\k. if k=0 then NONE else SOME(k-1))
            (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
      | AsmPushOfst l d => hj = hi+1 /\
          inherit (\k. if k=0 then NONE else SOME(k-1))
            (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
      | AsmOp name =>
          (case ALOOKUP dup_table name of
             SOME n => n < hi /\ hj = hi+1 /\
               inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0 < n /\ n < hi /\ hj = hi /\
                 inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
             | NONE => !a. a = asm_op_arity name ==> !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !s u. LENGTH s.as_stack=hi /\
                     asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
                       ins s = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
      | _ => F) ==>
  !Target. Target = (\p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\ off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME (pc y)) ==>
  !Structure. Structure = (\p (V:(num#num)->bool) (rank:(num#num)->num) pc height tag boolean edge.
    !x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
      Flow p pc height tag boolean x y /\
      (if EL (pc x) p = AsmOp "JUMP" then Target p pc tag x y
       else if EL (pc x) p = AsmOp "JUMPI" then pc y=pc x+1 \/ Target p pc tag x y
       else pc y=pc x+1)) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) rank pc height need tag boolean edge.
    FINITE V /\ (!x. x IN V ==> ?s. Shape p cc req pc height need tag boolean x s) /\
    (!x. x IN V ==> pc x < LENGTH p) /\
    Structure p V rank pc height tag boolean edge /\
    (!x s. x IN V /\ Shape p cc req pc height need tag boolean x s ==>
      (?u. (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 s = AsmRevert u \/
            asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 s = AsmFault u) /\
            u.as_requests=req) \/
      (?y u. edge x y /\
        asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 s = AsmOK u /\
        Shape p cc req pc height need tag boolean y u))) ==>
  !Slots. Slots = (\p (cc:call_context) (V:(num#num)->bool) height need tag boolean.
    !x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
        k < height x /\ origin < LENGTH p /\
        (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
        ?off dest. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
          off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) ==>
  !Rows. Rows = (\p (cc:call_context) (V:(num#num)->bool) pc height tag edge.
    !x. x IN V ==>
      pc x < LENGTH p /\
      !h. h = height x ==>
      !fall. fall = (?y. edge x y /\ pc y=pc x+1) ==>
      !taken. taken = (?y. edge x y /\ Target p pc tag x y) ==>
      !out. out = (\h'. !y. edge x y ==> height y=h') ==>
      !consumed. consumed = (\n. !k. k<n ==> tag x k=NONE) ==>
      !terminal. terminal = (!y. ~edge x y) ==>
      case EL (pc x) p of
        AsmLabel l => fall /\ out h
      | AsmPush bs => fall /\ out (h+1)
      | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ fall /\ out (h+1)
      | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ fall /\ out (h+1)
      | AsmOp name =>
          (name="INVALID" /\ terminal) \/
          (name="REVERT" /\ 2<=h /\ consumed 2 /\ terminal) \/
          (MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] /\
            cc.cc_static /\ asm_op_arity name<=h /\ consumed (asm_op_arity name) /\ terminal) \/
          (case ALOOKUP dup_table name of
             SOME n => n<h /\ fall /\ out (h+1)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0<n /\ n<h /\ fall /\ out h
             | NONE =>
                 (name="JUMP" /\ 1<=h /\ taken /\ out (h-1)) \/
                 (name="JUMPI" /\ 2<=h /\ tag x 1=NONE /\ fall /\ taken /\ out (h-2)) \/
                 (?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                      consumed (asm_op_arity name) /\ fall /\ out (h-asm_op_arity name+m)))
      | _ => F) ==>
  !Just. Just = (\ss tag boolean (e:num#num).
    (!k l origin. tag e k = SOME(l,origin) ==>
       k < LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
    (!k. boolean e k ==> k < LENGTH ss.sym_stack /\
       (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w))) ==>
  p = pre ++ [AsmOp "ISZERO";AsmOp "ISZERO";AsmPushLabel l;AsmOp "JUMPI"] ++ tail /\
  q = pre ++ [AsmPushLabel l;AsmOp "JUMPI"] ++ tail /\
  asm_static_wf p /\ asm_sym_rel p (asm_data_env p (assemble p ++ data)) a ss /\
  (?V e rank pc height need tag boolean edge.
     Open p a.as_call_ctx a.as_requests V rank pc height need tag boolean edge /\
     Rows p a.as_call_ctx V pc height tag edge /\
     Slots p a.as_call_ctx V height need tag boolean /\
     e IN V /\ (!x. x IN V ==>
       ?n (path:num->num#num). path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
     Shape p a.as_call_ctx a.as_requests pc height need tag boolean e a /\ Just ss tag boolean e) /\
  asm_sym_rel q (asm_data_env q (assemble q ++ data)) t u /\
  t.as_call_ctx=a.as_call_ctx /\ t.as_requests=a.as_requests /\
  (if b<c /\ c<b+4 then
     u.sym_base.as_pc=b /\ ?w stk. u.sym_stack=Val w::stk /\
       ss.sym_stack=(if c-b=3 then [Lab l 0] else []) ++
         (Val (FUNPOW (\w:bytes32. (b2w (w=0w):bytes32)) (MIN (c-b) 2) w)::stk)
   else u=sym_with_pc (splice_pc b 4 2 c) ss) ==>
  ?V e rank pc height need tag boolean edge.
    FINITE V /\ e IN V /\ Rows q t.as_call_ctx V pc height tag edge /\
    Structure q V rank pc height tag boolean edge /\
    Slots q t.as_call_ctx V height need tag boolean /\
    Shape q t.as_call_ctx t.as_requests pc height need tag boolean e t /\ Just u tag boolean e
Proof
  map_every branch_intro [`b`,`c`,`Shape`,`Flow`,`Target`,`Structure`,`Open`,`Slots`,`Rows`,`Just`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?V e rank pc height need tag boolean edge. _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `Abbrev (Open = _)` (fn opn =>
    qpat_assum `Open p _ _ V rank pc height need tag boolean edge`
      (mp_tac o BETA_RULE o REWRITE_RULE[REWRITE_RULE[markerTheory.Abbrev_def] opn])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `keep = \i:num. i < b \/ b+2 <= i` >>
  qabbrev_tac `f = \i:num. if i < b then i else i-2` >>
  `?next. !x. x IN V ==>
      next x IN V /\ keep (pc (next x)) /\ height (next x)=height x /\
      (if keep (pc x) then next x=x else pc (next x)=b+2 /\ rank (next x)<rank x) /\
      (!k nm org. 0<k /\ tag (next x) k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
      (!k. 0<k /\ boolean (next x) k ==> boolean x k)` by suspend "selector" >>
  drule_then strip_assume_tac
    (SIMP_RULE (srw_ss()) []
       (ISPEC (pred_setSyntax.mk_univ ``:num # num``) IN_INFINITE_NOT_FINITE)) >>
  rename1 `v NOTIN V` >>
  qabbrev_tac `fresh = (c=b+3)` >>
  qabbrev_tac `verts_q = {x | x IN V /\ keep (pc x)} UNION (if fresh then {v} else {})` >>
  qabbrev_tac `root_q = if fresh then v else next e` >>
  qabbrev_tac `pc_q = \x. if x=v then b else f (pc x)` >>
  qabbrev_tac `height_q = \x. if x=v then height e-1 else height x` >>
  qabbrev_tac `rank_q = \x. if x=v then SUC (rank e) else rank x` >>
  qabbrev_tac `need_q = \x. x<>v /\ need x` >>
  qabbrev_tac `tag_q = \x k. if x=v then
      if k=0 then NONE else OPTION_MAP (\(nm,org). (nm,f org)) (tag e (k+1))
    else if pc x=b+2 /\ k=0 \/ pc x=b+3 /\ k=1 then NONE
    else if pc x=b+3 /\ k=0 then SOME(l,b)
    else OPTION_MAP (\(nm,org). (nm,f org)) (tag x k)` >>
  qabbrev_tac `bool_q = \x k. if x=v then 0<k /\ boolean e (k+1)
    else ~(pc x=b+2 /\ k=0 \/ pc x=b+3 /\ k<=1) /\ boolean x k` >>
  qabbrev_tac `edge_q = \x y. (x=v /\ fresh /\ y=e) \/
    (x IN V /\ keep (pc x) /\ ?z. edge x z /\ y=next z)` >>
  `pc e=c` by
    (qpat_assum `asm_sym_rel p _ a ss` (mp_tac o MATCH_MP asm_sym_rel_pc) >>
     qpat_assum `Shape p _ _ _ _ _ _ _ e a` mp_tac >>
     simp[NoAsms, Abbr `Shape`, Abbr `c`] >>
     disch_then (assume_tac o CONJUNCT1) >> simp[]) >>
  qabbrev_tac `Control = \p pc tag (x:num#num) (y:num#num).
    if EL (pc x) p = AsmOp "JUMP" then Target p pc tag x y
    else if EL (pc x) p = AsmOp "JUMPI" then pc y=pc x+1 \/ Target p pc tag x y
    else pc y=pc x+1` >>
  `!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
      Flow p pc height tag boolean x y /\ Control p pc tag x y` by
    (branch_with ["Structure","Control"] (fn cv => CONV_TAC cv) >>
     branch_exact ["Structure","Control"]) >>
  `!x. x IN V /\ EL (pc x) p = AsmOp "JUMPI" ==>
      2 <= height x /\ (?y. edge x y /\ Target p pc tag x y)` by suspend "jumpi" >>
  `!x y nm name org. edge x y /\ EL (pc x) p = AsmPushLabel nm /\
       tag y 0 = SOME(name,org) ==> name=nm` by suspend "push_tag" >>
  `fresh ==> ?stk. ss.sym_stack=Lab l 0::stk` by suspend "fresh_stack" >>
  `!x. x IN V /\ x<>e ==> ?w. edge w x` by suspend "path_last" >>
  `!x z. x IN V /\ keep (pc x) /\ edge x z /\ pc z=pc x+1 ==>
         f (pc (next z))=f (pc x)+1` by suspend "fall" >>
  `(!x. x IN V /\ pc x=b+3 ==> ?i. tag x 0=SOME(l,i)) /\
   (!x z. x IN V /\ keep (pc x) /\ edge x z ==>
      (pc z=pc x+1 ==> pc_q (next z)=pc_q x+1) /\
      ((EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
       Target p pc tag x z ==> Target q pc_q tag_q x (next z)) /\
      (pc (next z)=b+3 ==> next z=z /\ pc x=b+2)) /\
   (!x y. edge_q x y ==> x IN verts_q /\ y IN verts_q /\ rank_q y<rank_q x /\
      Control q pc_q tag_q x y)` by suspend "control" >>
  `Rows q t.as_call_ctx verts_q pc_q height_q tag_q edge_q` by suspend "rows" >>
  `Structure q verts_q rank_q pc_q height_q tag_q bool_q edge_q` by suspend "structure" >>
  `Slots q t.as_call_ctx verts_q height_q need_q tag_q bool_q` by suspend "slots" >>
  `Shape q t.as_call_ctx t.as_requests pc_q height_q need_q tag_q bool_q root_q t /\
   Just u tag_q bool_q root_q` by suspend "root_shape" >>
  qexistsl_tac [`verts_q`,`root_q`,`rank_q`,`pc_q`,`height_q`,`need_q`,`tag_q`,`bool_q`,`edge_q`] >>
  conj_tac >- suspend "finite" >>
  conj_tac >- suspend "root_member" >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume merge_iszero_jumpi_cut_table[selector]:
  `!i. i=b \/ i=b+1 ==> asm_block_at p i (REPLICATE (b+2-i) (AsmOp "ISZERO"))` by
    (qx_gen_tac `i` >> strip_tac >>
     mp_tac (Q.SPECL [`pre`,`l`,`tail`,`b`,`p`,`i`] branch_test_suffix) >>
     simp[Abbr `b`]) >>
  simp[NoAsms, Abbr `keep`] >>
  mp_tac (CONV_RULE branch_norm (Q.SPECL
    [`p`,`a.as_call_ctx`,`a.as_requests`,`V`,`rank`,`pc`,`height`,`need`,
     `tag`,`boolean`,`edge`,`b`] merge_iszero_branch_selector)) >>
  (impl_tac >-
    (reverse conj_tac >- first_assum ACCEPT_TAC >>
     branch_with ["Open","Structure","Target","Flow","Shape"] (fn cv =>
       rewrite_tac[boolTheory.OR_CLAUSES] >>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [boolTheory.OR_CLAUSES] o CONV_RULE cv)))) >>
  disch_then ACCEPT_TAC
QED


Resume merge_iszero_jumpi_cut_table[jumpi]:
  qx_gen_tac `x` >> strip_tac >>
  qpat_assum `Rows p _ V pc height tag edge` mp_tac >>
  simp[NoAsms, Abbr `Rows`] >>
  disch_then (qspec_then `x` (drule_then (mp_tac o CONJUNCT2))) >>
  simp[EVAL ``ALOOKUP dup_table "JUMPI"``, EVAL ``ALOOKUP swap_table "JUMPI"``,
       static_abort_straight_def]
QED

Resume merge_iszero_jumpi_cut_table[push_tag]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x y. edge x y ==> _ /\ _ /\ _ /\ Flow _ _ _ _ _ x y /\ _`
    (drule_then (mp_tac o cj 4)) >>
  branch_with ["Flow"] (fn cv => CONV_TAC cv) >>
  qpat_assum `EL (pc x) p = AsmPushLabel nm` (fn th =>
    simp[NoAsms, th]) >>
  disch_then (fn th => mp_tac (Q.SPECL [`0`,`name`,`org`] (cj 2 th))) >>
  simp[]
QED

Resume merge_iszero_jumpi_cut_table[fresh_stack]:
  simp[NoAsms, Abbr `fresh`] >> disch_tac >>
  `b<c /\ c<b+4 /\ c-b=3` by decide_tac >>
  qpat_assum `(if b<c /\ c<b+4 then _ else _)` (fn endpoint =>
    qpat_assum `c-b=3` (fn offset =>
      qpat_assum `b<c` (fn lower =>
        qpat_assum `c<b+4` (fn upper =>
          strip_assume_tac (SRULE [lower,upper,offset] endpoint))))) >>
  goal_assum (drule_at Any)
QED

Resume merge_iszero_jumpi_cut_table[path_last]:
  qx_gen_tac `x` >> strip_tac >>
  qpat_assum `!x. x IN V ==> ?n path. path 0=e /\ path n=x /\ _`
    (drule_then (mp_tac o MATCH_MP branch_path_last)) >> simp[]
QED

Resume merge_iszero_jumpi_cut_table[fall]:
  rpt gen_tac >> strip_tac >>
  `z IN V` by metis_tac[] >>
  qpat_assum `!x. x IN V ==> next x IN V /\ _`
    (qspec_then `z` (drule_then (assume_tac o cj 4))) >>
  branch_with ["keep","f"] (fn cv => CONV_TAC cv) >>
  irule (CONV_RULE branch_norm branch_relinked_fall) >>
  Cases_on `keep (pc z)` >> fs[Abbr `keep`]
QED

Resume merge_iszero_jumpi_cut_table[control]:
  `!x y. edge x y ==> x IN V /\ y IN V /\ rank y<rank x /\ Control p pc tag x y` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x y. edge x y ==> _ /\ _ /\ _ /\ Flow p pc height tag boolean x y /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!x. x IN V /\ EL (pc x) p = AsmOp "JUMPI" ==> ?y. edge x y /\ Target p pc tag x y` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. x IN V /\ EL (pc x) p = AsmOp "JUMPI" ==> 2 <= height x /\ _`
       (drule_all_then (ACCEPT_TAC o CONJUNCT2))) >>
  `!nm org. tag e 0=SOME(nm,org) ==> EL 0 ss.sym_stack=Lab nm 0` by
    (qpat_assum `Just ss tag boolean e` mp_tac >>
     simp[NoAsms, Abbr `Just`] >> metis_tac[]) >>
  (* Control observes only zero; its selector premise also uses positive
     indices. Embed the zero slot and use slot one for every positive index. *)
  qabbrev_tac `ctag = \x (k:rat). tag x (if k=0 then 0 else 1)` >>
  qabbrev_tac `cbool = \(x:num#num) (k:rat). F` >>
  `!x. x IN V ==> next x IN V /\ keep (pc (next x)) /\ height (next x)=height x /\
       (if keep (pc x) then next x=x else pc (next x)=b+2 /\ rank (next x)<rank x) /\
       (!k nm org. (0:rat)<k /\ ctag (next x) k=SOME(nm,org) ==> ctag x k=SOME(nm,org)) /\
       (!k. (0:rat)<k /\ cbool (next x) k ==> cbool x k)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. x IN V ==> next x IN V /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     simp[Abbr `cbool`, Abbr `ctag`] >>
     rpt strip_tac >>
     `k <> (0:rat)` by (strip_tac >> gvs[]) >>
     gvs[] >> metis_tac[DECIDE ``0 < 1:num``]) >>
  `!x. ctag x (0:rat) = tag x (0:num)` by simp[Abbr `ctag`] >>
  qpat_assum `!x. ctag x (0:rat) = tag x (0:num)` (fn top_slot =>
    branch_with ["Target","Control","tag_q","edge_q"] (fn cv =>
      branch_shared ["V","e","rank","pc","height","ctag","cbool","edge","next","v"]
        [SOME "b",SOME "c",SOME "keep",SOME "f",SOME "fresh",SOME "verts_q",
         SOME "pc_q",SOME "rank_q",NONE,NONE,NONE,NONE]
        merge_iszero_branch_control (fn th => mp_tac (CONV_RULE branch_norm th)) >>
      (impl_tac >-
        (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
          (CONV_TAC cv >> simp[NoAsms, top_slot] >>
           first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [top_slot] o CONV_RULE cv))))) >>
      let
        val slots = [top_slot, DECIDE ``(0:num) <> 1``,
          MATCH_MP ratTheory.RAT_LES_IMP_NEQ ratTheory.RAT_LES_01]
      in
        disch_then (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss slots) >>
        CONV_TAC cv >> SIMP_TAC bool_ss slots >> rpt conj_tac >> first_assum ACCEPT_TAC
      end))
QED

Resume merge_iszero_jumpi_cut_table[finite]:
  simp[Abbr `verts_q`, FINITE_UNION] >> conj_tac
  >- (irule SUBSET_FINITE >> qexists_tac `V` >> simp[SUBSET_DEF]) >>
  Cases_on `fresh` >> simp[]
QED

Resume merge_iszero_jumpi_cut_table[root_member]:
  Cases_on `fresh` >- simp[Abbr `root_q`, Abbr `verts_q`] >>
  qpat_assum `!x. x IN V ==> next x IN V /\ _` (qspec_then `e` mp_tac) >>
  simp[Abbr `root_q`, Abbr `verts_q`]
QED

Resume merge_iszero_jumpi_cut_table[rows]:
  `!x z. edge x z ==> z IN V` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x z. edge x z ==> _ /\ _ /\ _ /\ Flow _ _ _ _ _ x z /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!x z. x IN V /\ keep (pc x) /\ edge x z ==>
    (pc z=pc x+1 ==> pc_q (next z)=pc_q x+1) /\
    ((EL (pc x) p=AsmOp "JUMP" \/ EL (pc x) p=AsmOp "JUMPI") /\
     Target p pc tag x z ==> Target q pc_q tag_q x (next z))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x z. x IN V /\ keep (pc x) /\ edge x z ==> _ /\ _ /\ _`
       (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `drank = \x. rat_of_num (rank x)` >>
  qabbrev_tac `dbool = \(x:num#num) (k:rat). F` >>
  branch_with ["verts_q","height_q","edge_q"] (fn cv =>
    branch_shared ["p","q","pre","l","tail","ss","a","t","V","e","drank","pc","height",
                   "tag","dbool","edge","next","v"]
      [SOME "b",SOME "c",SOME "Target",SOME "Rows",SOME "keep",SOME "f",SOME "fresh",
       SOME "pc_q",NONE,SOME "tag_q"]
      merge_iszero_branch_dispatch (mp_tac o CONV_RULE branch_norm) >>
    (impl_tac >- (rpt conj_tac >> FIRST
       [first_assum ACCEPT_TAC, first_assum (ACCEPT_TAC o CONV_RULE cv),
        gen_tac >> disch_tac >>
        qpat_assum `!x. x IN V ==> next x IN V /\ _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >>
        simp[Abbr `drank`, Abbr `dbool`, ratTheory.RAT_OF_NUM_LES]])) >>
    CONV_TAC cv >> disch_then ACCEPT_TAC)
QED

Resume merge_iszero_jumpi_cut_table[structure]:
  `EL (b+3) p = AsmOp "JUMPI"` by
    simp[Abbr `b`, EL_APPEND_EQN] >>
  `!x. x IN V /\ pc x=b+3 ==> 2 <= height x` by
    (gen_tac >> strip_tac >>
     `EL (pc x) p = AsmOp "JUMPI"` by metis_tac[] >>
     qpat_assum `!x. x IN V /\ EL (pc x) p = AsmOp "JUMPI" ==> 2 <= height x /\ _`
       (drule_all_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!x. x IN V ==>
     (!k nm org. tag x k=SOME(nm,org) ==> k<height x) /\
     (!k. boolean x k ==> k<height x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `Slots p _ V height need tag boolean` mp_tac >>
     simp[NoAsms, Abbr `Slots`] >> disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  `!x z. Control p pc tag (x:num#num) (z:num#num) ==>
     (EL (pc x) p <> AsmOp "JUMP" /\ EL (pc x) p <> AsmOp "JUMPI" ==>
      pc z=pc x+1)` by
    (branch_with ["Control"] (fn cv => CONV_TAC cv) >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     Cases_on `EL (pc x) p = AsmOp "JUMP"` >>
     Cases_on `EL (pc x) p = AsmOp "JUMPI"` >> simp[]) >>
  `!x z. edge x z ==> z IN V /\ Flow p pc height tag boolean x z /\
     (EL (pc x) p <> AsmOp "JUMP" /\ EL (pc x) p <> AsmOp "JUMPI" ==>
      pc z=pc x+1)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x z. edge x z ==> _ /\ _ /\ _ /\ Flow p pc height tag boolean x z /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
     qpat_assum `!x z. Control p pc tag x z ==> _` (drule_then ACCEPT_TAC)) >>
  `!x z. x IN V /\ keep (pc x) /\ edge x z /\ pc (next z)=b+3 ==>
     next z=z /\ pc x=b+2` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x z. x IN V /\ keep (pc x) /\ edge x z ==> _ /\ _ /\ _`
       (drule_all_then (map_every assume_tac o CONJUNCTS)) >> (simp[])) >>
  `!x y. edge_q x y ==> Flow q pc_q height_q tag_q bool_q x y` by
    (branch_with ["edge_q","fresh","pc_q","height_q","tag_q","bool_q"] (fn cv =>
       branch_shared [] [NONE,SOME "Flow"] merge_iszero_branch_flow
         (fn flow =>
           branch_shared ["p","q","pre","tail","l","V","e","c","rank","pc","height",
                          "tag","boolean","edge","next","v"]
             [SOME "b",SOME "keep",SOME "f",NONE] flow
             (mp_tac o CONV_RULE branch_norm)) >>
       (impl_tac >- (rpt conj_tac >> FIRST
         [first_assum ACCEPT_TAC, first_assum (ACCEPT_TAC o CONV_RULE cv)])) >>
       CONV_TAC cv >> disch_then ACCEPT_TAC)) >>
  simp[NoAsms, Abbr `Structure`] >> rpt gen_tac >> disch_tac >>
  qpat_assum `!x y. edge_q x y ==> x IN verts_q /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!x y. edge_q x y ==> Flow _ _ _ _ _ x y` (drule_then assume_tac) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE branch_exact ["Control"])
QED

Resume merge_iszero_jumpi_cut_table[slots]:
  qabbrev_tac `slot_bool = \x k. if x=v then 0<k /\ boolean e (k+1)
    else boolean x k /\ ~(pc x=b+2 /\ k=0) /\ ~(pc x=b+3 /\ k<=1)` >>
  `slot_bool = bool_q` by
    (simp[NoAsms, Abbr `slot_bool`, Abbr `bool_q`, FUN_EQ_THM] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     IF_CASES_TAC >> simp[AC CONJ_ASSOC CONJ_COMM]) >>
  branch_shared ["pre","tail","p","q","l","ss","t","V","e","pc","height","need",
                 "tag","boolean","v"]
    [SOME "b",NONE,SOME "Slots"]
    merge_iszero_branch_slots (mp_tac o CONV_RULE branch_norm) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `t.as_call_ctx = a.as_call_ctx` SUBST1_TAC >> first_assum ACCEPT_TAC)))) >>
  qpat_assum `slot_bool = bool_q` (fn eq =>
    once_rewrite_tac[GSYM eq] >>
    branch_with ["verts_q","fresh","c","keep","height_q","need_q","tag_q","f","slot_bool"]
      (fn dst => CONV_TAC dst) >>
    disch_then ACCEPT_TAC)
QED

Resume merge_iszero_jumpi_cut_table[root_shape]:
  branch_with ["verts_q","pc_q"] (fn cv =>
    branch_shared []
      [SOME "b",SOME "c",SOME "Shape",SOME "Just",SOME "Slots",
       SOME "keep",SOME "f",SOME "fresh",NONE,SOME "root_q",
       SOME "height_q",SOME "need_q",SOME "tag_q",SOME "bool_q"]
      (INST_TYPE [alpha |-> ``:asm_inst``] merge_iszero_branch_actual_root)
      (mp_tac o CONV_RULE branch_norm) >>
    (impl_tac >- (rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE first_assum (ACCEPT_TAC o CONV_RULE cv)))) >>
    CONV_TAC cv >> disch_then ACCEPT_TAC)
QED

Finalise merge_iszero_jumpi_cut_table
