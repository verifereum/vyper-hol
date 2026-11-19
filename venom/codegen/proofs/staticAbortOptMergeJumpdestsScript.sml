(* Transport the protected exception and the covered cut separately. *)
Theory staticAbortOptMergeJumpdests
Ancestors
  staticAbortOptMergeJumpdestsWalk staticAbortOptMergeJumpdestsAssemble
  asmOptMergeJumpdests asmSplice codegenSymRel asmSymBridge asmDataEnv
  finalizerContract asmSymSem asmSem asmIR staticAbortStraight
  finite_map pred_set list words

(* Normalize naming guards only at the boundaries of the folded contracts. *)
val names_conv = TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV)

(* The matching concrete exception and symbolic termination use one count. *)
Theorem merge_protected_terminal[local]:
  !env. env = asm_data_env orig (assemble orig ++ data) ==>
  !run. run = (\r n. asm_steps (SND (compute_label_offsets r)) (build_offset_to_pc r)
                    r n (s with as_code := assemble r ++ data)) ==>
  s.as_pc = 0 /\ asm_static_wf orig /\ asm_static_wf p /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\ asm_refines p q /\
  (run p n = AsmRevert out \/ run p n = AsmFault out) /\
  sym_terminal (sym_steps p env n (sym_init s)) ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig /\
  ?m t. (run q m = AsmRevert t \/ run q m = AsmFault t) /\
        sym_terminal (sym_steps q env m (sym_init s)) /\
        t.as_requests = out.as_requests
Proof
  CONV_TAC names_conv >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `env = asm_data_env orig (assemble orig ++ data)` >>
  qabbrev_tac `start = s with as_code := assemble p ++ data` >>
  qabbrev_tac `dest = s with as_code := assemble q ++ data` >>
  `start.as_pc = 0 /\ dest.as_pc = 0 /\ sym_init start = sym_init s /\ sym_init dest = sym_init s` by
    simp[Abbr `start`, Abbr `dest`, sym_init_def] >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig` by
    fs[asm_refines_def] >>
  `asm_data_env_ok p env start.as_code /\ asm_data_env_ok q env dest.as_code` by
    (simp[Abbr `start`, Abbr `dest`] >> conj_tac
     >- (`env = asm_data_env p (assemble p ++ data)` by
           (simp[Abbr `env`] >> irule asm_data_env_agree >> simp[]) >>
         simp[asm_data_env_ok_asm_data_env]) >>
     `env = asm_data_env q (assemble q ++ data)` by
       (simp[Abbr `env`] >> irule asm_data_env_agree >> simp[]) >>
     simp[asm_data_env_ok_asm_data_env]) >>
  `sym_run p env n (sym_init s) = sym_steps p env n (sym_init s)` by
    (drule_then (qspec_then `0` mp_tac) sym_steps_terminal_run >> simp[]) >>
  `label_disciplined env p start` by
    (irule sym_terminal_disciplined >> (metis_tac[])) >>
  `sym_terminal (asm_result_sym (asm_steps (SND (compute_label_offsets p))
     (build_offset_to_pc p) p n start))` by
    (qpat_assum `_ = AsmRevert out \/ _ = AsmFault out` DISJ_CASES_TAC >>
     simp[asm_result_sym_def,sym_terminal_def]) >>
  drule_all asm_sym_forward >> strip_tac >>
  `sym_run p env fuel (sym_init start) = sym_steps p env n (sym_init s)` by
    (qpat_assum `sym_result_rel _ (sym_run p env fuel _)`
       (strip_assume_tac o MATCH_MP sym_result_rel_terminal) >>
     drule_then (qspec_then `n` mp_tac) (GEN_ALL sym_run_terminal_steps) >>
     simp[] >> Cases_on `sym_steps p env n (sym_init s)` >> fs[sym_terminal_def]) >>
  suspend "refinement"
QED

Resume merge_protected_terminal[refinement]:
  `?fuel'. sym_result_rel (sym_run p env n (sym_init s))
                       (sym_run q env fuel' (sym_init s))` by
    (qpat_assum `asm_refines p q` (mp_tac o REWRITE_RULE [asm_refines_def]) >>
     impl_tac >- simp[] >> disch_then (mp_tac o cj 3) >>
     disch_then (qspecl_then [`env`,`s`,`n`] mp_tac) >> simp[]) >>
  `sym_terminal (sym_run q env fuel' (sym_init dest))` by
    metis_tac[sym_result_rel_terminal] >>
  drule_all asm_sym_backward >> strip_tac >>
  rename1 `sym_result_rel (sym_run q env fuel' _) (asm_result_sym (asm_steps _ _ q m dest))` >>
  `!a. sym_steps q env m (sym_init dest) <> SymOK a` by
    (rpt strip_tac >>
     `asm_sym_rel q env dest (sym_init dest)` by (irule asm_sym_rel_init >> simp[]) >>
     drule_all asm_sym_steps_lockstep >> strip_tac >>
     qpat_assum `sym_result_rel (sym_run q env fuel' _) _`
       (mp_tac o cj 2 o MATCH_MP sym_result_rel_terminal) >>
     simp[asm_result_sym_def,sym_terminal_def]) >>
  `sym_run q env fuel' (sym_init dest) = sym_steps q env m (sym_init s)` by
    (qpat_assum `sym_terminal (sym_run q env fuel' (sym_init dest))`
       (mp_then Any (qspec_then `m` mp_tac) (GEN_ALL sym_run_terminal_steps)) >> simp[]) >>
  `sym_result_rel (asm_result_sym (asm_steps (SND (compute_label_offsets p))
     (build_offset_to_pc p) p n start))
     (asm_result_sym (asm_steps (SND (compute_label_offsets q))
        (build_offset_to_pc q) q m dest))` by
    metis_tac[sym_result_rel_trans] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `m` >>
  `sym_terminal (sym_steps q env m (sym_init s))` by metis_tac[] >>
  qpat_assum `_ = AsmRevert out \/ _ = AsmFault out` DISJ_CASES_TAC >>
  Cases_on `asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q m dest` >>
  qpat_x_assum `sym_result_rel (asm_result_sym (asm_steps _ _ p n start)) _` mp_tac >>
  simp[asm_result_sym_def,sym_result_rel_def,sym_obs_def,sym_init_def,
       asm_state_component_equality] >> metis_tac[]
QED

Finalise merge_protected_terminal

fun bind_names names =
  map_every (fn k => gen_tac >> disch_then (mk_asm k)) names
fun open_names names =
  map_every (fn k => asm k (pure_rewrite_tac o single)) names >>
  CONV_TAC names_conv
fun named_equations [] k = k []
  | named_equations (name::names) k =
      asm name (fn th => named_equations names (fn eqs => k (th::eqs)))
fun unfold_fact names pat ttac = named_equations names
  (fn eqs => qpat_assum pat (ttac o CONV_RULE names_conv o PURE_REWRITE_RULE eqs))

(* The closed Rows boundary presents the same lookup witnesses in the
   opposite quantifier order in the elementary transport theorem. *)
Theorem merge_rows_lookup_order[local]:
  (?j off. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
           FLOOKUP otp off = SOME j) <=>
  (?off j. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
           FLOOKUP otp off = SOME j)
Proof
  metis_tac[]
QED

fun closed_cert th = PURE_REWRITE_RULE
  [merge_rows_lookup_order, EMPTY_SUBSET, DIFF_EMPTY, GSYM CONJ_ASSOC] th

local
  val rule = closed_cert (CONV_RULE names_conv merge_rename_covered_cut)
  val names = [("p0","orig"), ("p","pp"), ("final_req","req_bound"),
               ("n","j"), ("f","u"), ("cut","t")]
in
  fun apply_merge_site (asms,g) = let
    val vars = List.concat (map free_vars (g::asms))
    fun image v = let
      val (name,ty) = dest_var v
      val target = case List.find (fn (a,_) => a = name) names of
          SOME (_,b) => b | NONE => name
      in case List.find (fn w => dest_var w = (target,ty)) vars of
          SOME w => v |-> w
        | NONE => raise Fail ("merge site: missing variable " ^ target)
      end
    in mp_tac (INST (map image (free_vars (concl rule))) rule) (asms,g) end
end

fun exact_packet g =
  (FIRST [first_assum ACCEPT_TAC, ACCEPT_TAC TRUTH,
          conj_tac >> exact_packet]) g

Theorem merge_jumpdests_abort_certificate:
  !orig (s:asm_state) data req_bound.
  !Shape. Shape = (\p cc req pc height need tag boolean i (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest.
         FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\
         FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !target. target = (\p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) p ==>
    !inherit. inherit =
      (\(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
             ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
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
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + asm_op_arity name - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t=AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Rows. Rows = (\p cc V rank pc height need tag boolean edge.
    !lo. lo = SND (compute_label_offsets p) ==>
    !otp. otp = build_offset_to_pc p ==>
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                    FLOOKUP otp off = SOME dest)) /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow p pc height tag boolean x y) /\
    (!x. x IN V ==>
      pc x < LENGTH p /\
      (!h. h = height x ==>
       !fall. fall = (\y. pc y = pc x+1) ==>
       !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
       !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
       !next. next = (\n. arm fall n /\ legal fall n) ==>
       !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
       !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
       case EL (pc x) p of
         AsmLabel l => next h
       | AsmPush bs => next (h+1)
       | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
       | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
       | AsmOp name =>
           if name="INVALID" then stop 0
           else if name="REVERT" then stop 2
           else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
                then cc.cc_static /\ stop (asm_op_arity name)
           else
             (case ALOOKUP dup_table name of
                SOME n => n<h /\ next (h+1)
              | NONE => case ALOOKUP swap_table name of
                  SOME n => 0<n /\ n<h /\ next h
                | NONE =>
                    if name="JUMP" then
                       1<=h /\ arm (target p pc tag x) (h-1) /\ legal (target p pc tag x) (h-1)
                    else if name="JUMPI" then
                       2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target p pc tag x) (h-2) /\
                       legal (\y. fall y \/ target p pc tag x y) (h-2)
                    else
                       ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                           untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
       | _ => F))) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target p pc tag x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ S x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))) ==>
  !Reach. Reach = (\(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) ==>
  !bytes. bytes = (\p. assemble p ++ data) ==>
  !env0. env0 = asm_data_env orig (bytes orig) ==>
  !run. run = (\p n. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n
                     (s with as_code := bytes p)) ==>
  !Base. Base = (\p. s.as_pc = 0 /\ s.as_code = bytes orig /\
                 asm_static_wf orig /\ asm_static_wf p /\
                 FILTER is_data_inst p = FILTER is_data_inst orig) ==>
  !Terminal. Terminal = (\p. ?n out.
    (run p n = AsmRevert out \/ run p n = AsmFault out) /\
    sym_terminal (sym_steps p env0 n (sym_init s)) /\
    out.as_requests <<= req_bound) ==>
  !Cut. Cut = (\p.
    ?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
      pc height need tag boolean edge.
      run p j = AsmOK t /\
      sym_steps p env0 j (sym_init s) = SymOK u /\
      asm_sym_rel p (asm_data_env p (bytes p)) t u /\
      t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
      t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
      t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
      Rows p cc V rank pc height need tag boolean edge /\
      Open p cc req V {} rank pc height need tag boolean edge /\
      e IN V /\ (!x. x IN V ==> Reach edge e x) /\
      Shape p cc req pc height need tag boolean e t /\
      (!k l origin. tag e k = SOME(l,origin) ==>
         k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
      (!k. boolean e k ==>
         k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))) ==>
  !M_R. M_R = (\p. Base p /\ (Terminal p \/ Cut p)) ==>
    !p. M_R p ==> M_R (FST (merge_jumpdests p))
Proof
  ntac 4 gen_tac >>
  bind_names ["shape","mr_target","flow","rows","open","reach","mr_bytes","env","run",
             "base","terminal","cut","mixed"] >>
  open_names ["mixed"] >> gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac DISJ_CASES_TAC)
  >- suspend "terminal_arm" >>
  `Base (FST (merge_jumpdests p)) /\ Cut (FST (merge_jumpdests p))` suffices_by
    (strip_tac >> simp[]) >>
  qabbrev_tac `P = \r. Base r /\ Cut r` >>
  `P p` by simp[Abbr `P`] >>
  `P (FST (merge_jumpdests p))` suffices_by simp[Abbr `P`] >>
  irule merge_jumpdests_walk_preserves_contextual >>
  `!pre x next third tail y.
     ((next = AsmLabel y /\ y <> x) \/ (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
     P (pre ++ [AsmLabel x; next; third] ++ tail) ==>
     P (MAP (rename_push_label x y) (pre ++ [AsmLabel x; next; third] ++ tail))`
    by suspend "site" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >> rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[]
QED

Resume merge_jumpdests_abort_certificate[terminal_arm]:
  unfold_fact ["base","mr_bytes"] `Base p` (map_every assume_tac o CONJUNCTS) >>
  unfold_fact ["terminal","run","env","mr_bytes"] `Terminal p`
    (qx_choose_then `n` (qx_choose_then `out` (map_every assume_tac o CONJUNCTS))) >>
  `asm_refines p (FST (merge_jumpdests p))` by simp[merge_jumpdests_refines] >>
  drule_all (CONV_RULE names_conv merge_protected_terminal) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `m` (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))))) >>
  conj_tac >- (open_names ["base","mr_bytes"] >> simp[]) >>
  disj1_tac >> open_names ["terminal","run","env","mr_bytes"] >>
  qexistsl [`m`,`t`] >> simp[]
QED

Resume merge_jumpdests_abort_certificate[site]:
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qabbrev_tac `pp = pre ++ [AsmLabel x; next; third] ++ tail` >>
  `pp = pre ++ [AsmLabel x; next; third] ++ tail` by simp[Abbr `pp`] >>
  qpat_assum `Abbrev (P = _)` (fn th =>
    qpat_assum `P pp` (strip_assume_tac o CONV_RULE names_conv o
      PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
  unfold_fact ["base","mr_bytes"] `Base pp` (map_every assume_tac o CONJUNCTS) >>
  unfold_fact ["cut","run","env","mr_bytes"] `Cut pp`
    (qx_choose_then `j` (qx_choose_then `t` (qx_choose_then `u` (qx_choose_then `cc`
      (qx_choose_then `req` strip_assume_tac))))) >>
  rename1 `Rows pp cc V rank pc height need tag boolean edge` >>
  rename1 `Shape pp cc req pc height need tag boolean e t` >>
  unfold_fact ["open","shape","flow","mr_target"] `Open pp cc req V {} rank pc height need tag boolean edge`
    (map_every assume_tac o CONJUNCTS o closed_cert) >>
  unfold_fact ["rows","flow","mr_target"] `Rows pp cc V rank pc height need tag boolean edge`
    (map_every assume_tac o CONJUNCTS o closed_cert) >>
  unfold_fact ["shape"] `Shape pp cc req pc height need tag boolean e t`
    (map_every assume_tac o CONJUNCTS o closed_cert) >>
  unfold_fact ["reach"] `!v. v IN V ==> Reach edge e v` assume_tac >>
  apply_merge_site >>
  (impl_tac >- exact_packet) >>
  disch_tac >> pop_assum (map_every (fn th =>
    if is_exists (concl th) then
      let
        val (binders,_) = strip_exists (concl th)
        val names = ["out_n","out_sym","out_state","out_vertices","out_root","out_rank",
                     "out_pc","out_height","out_need","out_tag","out_bool","out_edge"]
        val vars = ListPair.mapEq (fn (name,v) => mk_var (name,type_of v)) (names,binders)
      in List.foldr (fn (v,k) => X_CHOOSE_THEN v k)
           (map_every assume_tac o CONJUNCTS) vars th end
    else assume_tac th) o CONJUNCTS) >>
  `out_state.as_pc = out_sym.sym_base.as_pc /\
   LENGTH out_state.as_stack = LENGTH out_sym.sym_stack /\
   out_state.as_call_ctx = out_sym.sym_base.as_call_ctx /\
   out_state.as_requests = out_sym.sym_base.as_requests` by
    (qpat_assum `asm_sym_rel _ _ out_state out_sym`
       (strip_assume_tac o REWRITE_RULE [asm_sym_rel_def]) >>
     qpat_assum `out_sym.sym_base = _` (pure_rewrite_tac o single) >>
     simp[NoAsms] >> sym_tac >> drule LIST_REL_LENGTH >> simp[]) >>
  qpat_assum `Abbrev (P = _)`
    (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  CONV_TAC names_conv >> conj_tac
  >- (open_names ["base","mr_bytes"] >> exact_packet) >>
  open_names ["cut","run","env","mr_bytes"] >>
  qexistsl [`out_n`,`out_state`,`out_sym`,`cc`,`req`,`out_vertices`,
            `out_root`,`out_rank`,`out_pc`,`out_height`,`out_need`,`out_tag`,
            `out_bool`,`out_edge`] >>
  open_names ["rows","open","shape","flow","mr_target","reach"] >>
  pure_rewrite_tac [merge_rows_lookup_order, EMPTY_SUBSET, DIFF_EMPTY, GSYM CONJ_ASSOC] >>
  exact_packet
QED

Finalise merge_jumpdests_abort_certificate
