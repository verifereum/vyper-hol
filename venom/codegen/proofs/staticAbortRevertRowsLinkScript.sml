(* Retain the row and its exact interface through occurrence relinking. *)
Theory staticAbortRevertRowsLink
Ancestors
  staticAbortRevertLink staticAbortOpenFragmentCompose
  staticAbortLinkedArmInterfaces asmSem pred_set list arithmetic pair

Theorem revert_spine_link_rows:
  !(ixpc:num->num) lo_ix J len H p terminal normal cc req B.
  lo_ix <= J /\ len J = 1 /\
  (!i. lo_ix <= i /\ i < J ==>
    ixpc (SUC i) = ixpc i + len i /\ H (SUC i) 0 = H i (len i)) /\
  (!i s. lo_ix <= i /\ i <= J /\ s < len i ==>
    ixpc i+s < LENGTH p /\
    (if i = J then terminal (ixpc i+s) (H i s)
     else normal (ixpc i+s) (H i s) (H i (SUC s)))) /\
  (!i s t. lo_ix <= i /\ i <= J /\ s < len i /\
    t.as_pc = ixpc i+s /\ LENGTH t.as_stack = H i s /\
    t.as_call_ctx = cc /\ t.as_requests = req ==>
      (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmRevert u \/
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmFault u) /\
           u.as_requests = req) \/
      (i < J /\ ?u. asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\
          u.as_pc = ixpc i+SUC s /\ LENGTH u.as_stack = H i (SUC s) /\
          u.as_call_ctx = cc /\ u.as_requests = req)) /\
  (!i. lo_ix <= i /\ i <= J ==> len i <= B) ==>
  ?(W:(num#num)->bool) e rank pc height edge.
    FINITE W /\ e IN W /\ pc e = ixpc lo_ix /\ height e = H lo_ix 0 /\
    (!x. x IN W ==> pc x < LENGTH p /\
      (if FST x = J then terminal (pc x) (height x) /\ !y. ~edge x y
       else ?out. normal (pc x) (height x) out /\
         (?y. edge x y) /\ (!y. edge x y ==> pc y = pc x+1 /\ height y = out))) /\
    (!x y. edge x y ==> x IN W /\ y IN W /\ rank y < (rank x:num) /\
      FST x < J /\ pc y = pc x+1 /\ normal (pc x) (height x) (height y)) /\
    (!x. x IN W ==> ?n (path:num->num#num). path 0=e /\ path n=x /\
      !s. s<n ==> edge (path s) (path(SUC s))) /\
    (!x t. x IN W /\ t.as_pc = pc x /\ LENGTH t.as_stack = height x /\
      t.as_call_ctx = cc /\ t.as_requests = req ==>
      (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmRevert u \/
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmFault u) /\
           u.as_requests = req) \/
      (?y u. edge x y /\ asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\
          u.as_pc = pc y /\ LENGTH u.as_stack = height y /\
          u.as_call_ctx = cc /\ u.as_requests = req))
Proof
  rpt gen_tac >> strip_tac >>
  `0 < len J` by simp[] >> drule_all revert_active_targets >> strip_tac >>
  qabbrev_tac `V = {x:num#num | lo_ix <= FST x /\ FST x <= J /\
    (SND x < len (FST x) \/ SND x = len (FST x) /\ FST x < J)}` >>
  qabbrev_tac `X = {x:num#num | lo_ix <= FST x /\ FST x < J /\ SND x = len (FST x)}` >>
  qabbrev_tac `e = (next lo_ix,0:num)` >>
  qabbrev_tac `pc = \x:num#num. ixpc (FST x) + SND x` >>
  qabbrev_tac `height = \x:num#num. H (FST x) (SND x)` >>
  qabbrev_tac `out = \x:num#num. H (FST x) (SUC (SND x))` >>
  qabbrev_tac `Sh = \x (t:asm_state). t.as_pc = pc x /\ LENGTH t.as_stack = height x /\
    t.as_call_ctx = cc /\ t.as_requests = req` >>
  qabbrev_tac `iface = \x:num#num. (pc x,height x)` >>
  qabbrev_tac `arm_fits = \x (v:num#num). v = (pc x+1,out x)` >>
  qabbrev_tac `R = \x y. lo_ix <= FST x /\ FST x < J /\ SND x < len (FST x) /\
    y = (FST x,SUC (SND x))` >>
  qabbrev_tac `Good = \x. pc x < LENGTH p /\
    (if FST x = J then terminal (pc x) (height x) /\ (!y. ~R x y)
     else normal (pc x) (height x) (out x) /\ ?z. R x z /\ iface z = (pc x+1,out x))` >>
  qabbrev_tac `link = \z:num#num. (next (SUC (FST z)),0:num)` >>
  qabbrev_tac `lr = \x:num#num. len (FST x) - SND x` >>
  qabbrev_tac `ord = \i:num. J-i` >>
  `!x. x IN V DIFF X <=> lo_ix <= FST x /\ FST x <= J /\ SND x < len (FST x)` by
    (simp[Abbr `V`, Abbr `X`, IN_DIFF] >> decide_tac) >>
  `pc e = ixpc lo_ix /\ height e = H lo_ix 0 /\ e IN V DIFF X` by
    (qpat_assum `!i. lo_ix <= i /\ i <= J ==> _` (qspec_then `lo_ix` mp_tac) >>
     simp[Abbr `e`, Abbr `pc`, Abbr `height`]) >>
  qsuff_tac `FINITE V /\ X SUBSET V /\ e IN V DIFF X /\
    (!x. x IN V ==> lr x <= B /\ ?t. Sh x t) /\
    (!x. x IN V DIFF X ==> Good x) /\
    (!z. z IN X ==> link z IN V DIFF X /\ ord (FST (link z)) < ord (FST z) /\
       iface (link z) = iface z /\ (!t. Sh (link z) t <=> Sh z t)) /\
    (!x z. R x z ==> x IN V DIFF X /\ z IN V /\ FST x = FST z /\
      lr z < lr x /\ arm_fits x (iface z)) /\
    (!x t. x IN V DIFF X /\ Sh x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmRevert u \/
             asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmFault u) /\
            u.as_requests = req) \/
       (?z u. R x z /\ asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\ Sh z u))`
  >- suspend "restrict" >>
  rpt conj_tac
  >- (irule SUBSET_FINITE_I >> qexists `count (SUC J) CROSS count (SUC B)` >>
      simp[SUBSET_DEF, Abbr `V`] >> rpt strip_tac >>
      `len (FST x) <= B` by metis_tac[] >> decide_tac)
  >- simp[SUBSET_DEF, Abbr `V`, Abbr `X`]
  >- first_assum ACCEPT_TAC
  >- (simp[Abbr `V`, Abbr `lr`] >> rpt strip_tac >>
      TRY (`len (FST x) <= B` by metis_tac[] >> decide_tac) >>
      qexists `(ARB:asm_state) with <| as_pc := pc x; as_stack := REPLICATE (height x) 0w;
        as_call_ctx := cc; as_requests := req |>` >> simp[Abbr `Sh`])
  >- suspend "good"
  >- suspend "target"
  >- suspend "local_edge" >>
  simp[Abbr `Sh`, Abbr `pc`, Abbr `height`] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!i s t. _ ==> _ \/ _` drule_all >>
  disch_then (DISJ_CASES_THEN2 (fn th => simp[th]) strip_assume_tac) >>
  disj2_tac >> qexistsl [`(FST x,SUC (SND x))`,`u`] >> simp[Abbr `R`]
QED

Resume revert_spine_link_rows[good]:
  simp[Abbr `Good`, Abbr `pc`, Abbr `height`, Abbr `out`] >>
  gen_tac >> strip_tac >>
  qpat_assum `!i s. _ ==> _ /\ _` drule_all >> strip_tac >>
  Cases_on `FST x = J` >- fs[Abbr `R`] >>
  `FST x < J` by decide_tac >>
  qpat_assum `FST x <> J` (fn guard =>
    rewrite_tac [guard] >> conj_tac
    >- qpat_assum `if FST x = J then _ else _`
         (ACCEPT_TAC o REWRITE_RULE [guard])) >>
  qexists `(FST x,SUC (SND x))` >>
  asm_simp_tac bool_ss [Abbr `R`, Abbr `iface`, Abbr `arm_fits`, FST, SND, ADD1, ADD_ASSOC]
QED

Resume revert_spine_link_rows[target]:
  simp[Abbr `X`, Abbr `link`, Abbr `ord`] >> gen_tac >> strip_tac >>
  `lo_ix <= SUC (FST z) /\ SUC (FST z) <= J` by decide_tac >>
  qpat_assum `!i. lo_ix <= i /\ i <= J ==> _` drule_all >> strip_tac >>
  `ixpc (SUC (FST z)) = ixpc (FST z) + len (FST z) /\
    H (SUC (FST z)) 0 = H (FST z) (len (FST z))` by metis_tac[] >>
  simp[Abbr `iface`, Abbr `Sh`, Abbr `pc`, Abbr `height`] >> decide_tac
QED

Resume revert_spine_link_rows[restrict]:
  disch_then (fn prem =>
    strip_assume_tac prem >>
    mp_tac (MATCH_MP
      (SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss) [] open_fragment_compose) prem)) >>
  qabbrev_tac `redir = \x y. x IN V DIFF X /\ ?z. R x z /\ y = (if z IN X then link z else z)` >>
  qabbrev_tac `wnodes = {x | x IN V DIFF X /\
    ?n (path:num->num#num). path 0=e /\ path n=x /\
      !s. s<n ==> redir (path s) (path(SUC s))}` >>
  qabbrev_tac `rrank = \x:num#num. ord (FST x) * (B+1) + lr x` >>
  disch_then (fn th =>
    let val cs = CONJUNCTS th in
      EVERY [assume_tac (List.nth(cs,0)), assume_tac (List.nth(cs,1)),
        mk_asm "rows" (List.nth(cs,2)), mk_asm "close" (List.nth(cs,3)),
        mk_asm "paths" (List.nth(cs,4)), mk_asm "steps" (List.nth(cs,5))]
    end) >>
  `!x y. x IN wnodes /\ redir x y ==>
     y IN wnodes /\ rrank y < rrank x /\ pc y = pc x+1 /\ height y = out x` by
    (qpat_assum `Abbrev (arm_fits = _)` (fn af =>
     qpat_assum `Abbrev (iface = _)` (fn i =>
     asm "close" (ACCEPT_TAC o SIMP_RULE std_ss
       [REWRITE_RULE [markerTheory.Abbrev_def] af,
        REWRITE_RULE [markerTheory.Abbrev_def] i, PAIR_EQ])))) >>
  pop_assum (mk_asm "close_pair") >>
  qspecl_then [`V`,`X`,`e`,`R`,`link`,`iface`] mp_tac linked_reachable_arm_interfaces >>
  simp_tac (pure_ss ++ boolSimps.UNWIND_ss) [] >>
  (* Fold the same redirected relation and reachable set used above. *)
  qpat_assum `Abbrev (redir = _)` (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (wnodes = _)` (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (impl_tac >- (conj_tac
    >- (rpt gen_tac >> disch_tac >> qpat_assum `!x z. R x z ==> _` drule >> simp[])
    >> gen_tac >> disch_tac >> qpat_assum `!z. z IN X ==> _` drule >> simp[])) >>
  disch_then (mk_asm "arms") >>
  qabbrev_tac `edge = \x y. x IN wnodes /\ redir x y` >>
  `!x. x IN wnodes ==> Good x` by
    (gen_tac >> disch_tac >> asm "rows" (qspec_then `x` mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `!x y. edge x y ==> x IN wnodes /\ y IN wnodes /\ rrank y < rrank x /\
                       FST x < J /\ pc y = pc x+1 /\ height y = out x` by
    (rpt gen_tac >> simp[Abbr `edge`] >> strip_tac >>
     `FST x < J` by
       (qpat_assum `redir x y` mp_tac >>
        qpat_assum `Abbrev (redir = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `Abbrev (R = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        strip_tac >> (metis_tac[])) >>
     asm "close_pair" (qspecl_then [`x`,`y`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  qexistsl [`wnodes`,`e`,`rrank`,`pc`,`height`,`edge`] >>
  asm_simp_tac std_ss [] >>
  rpt conj_tac
  >- suspend "roles"
  >- suspend "edge_roles"
  >- (gen_tac >> disch_tac >> asm "paths" (qspec_then `x` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
      qexistsl [`n`,`path`] >> simp[Abbr `edge`] >> gen_tac >> strip_tac >>
      `s <= n` by decide_tac >> simp[])
  >- suspend "semantic_step"
QED

Resume revert_spine_link_rows[local_edge]:
  simp[Abbr `R`] >> rpt gen_tac >> strip_tac >>
  `FST x <= J` by decide_tac >>
  simp[Abbr `V`, Abbr `lr`, Abbr `arm_fits`, Abbr `iface`, Abbr `pc`, Abbr `height`, Abbr `out`] >>
  decide_tac
QED

Resume revert_spine_link_rows[roles]:
  gen_tac >> disch_tac >>
  `Good x` by (first_assum irule >> simp[]) >>
  `pc x < LENGTH p` by fs[Abbr `Good`] >>
  Cases_on `FST x = J`
  >- (`terminal (pc x) (height x)` by fs[Abbr `Good`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!x y. edge x y ==> _` drule >> simp[]) >>
  `normal (pc x) (height x) (out x) /\
   (?z. R x z /\ iface z = (pc x+1,out x))` by
    (fs[Abbr `Good`, Abbr `arm_fits`] >> qexists `z` >> simp[]) >>
  simp[] >> qexists `out x` >> simp[] >>
  asm "arms" (qspecl_then [`x`,`(pc x+1,out x)`] mp_tac) >>
  simp[Abbr `edge`] >> metis_tac[]
QED

Resume revert_spine_link_rows[edge_roles]:
  rpt gen_tac >> disch_tac >> qpat_assum `!x y. edge x y ==> _` drule >> strip_tac >>
  `Good x` by (first_assum irule >> simp[]) >>
  `FST x <> J` by decide_tac >> fs[Abbr `Good`]
QED

Resume revert_spine_link_rows[semantic_step]:
  rpt gen_tac >> strip_tac >>
  `Sh x t` by simp[Abbr `Sh`] >>
  asm "steps" (qspecl_then [`x`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (DISJ_CASES_THEN2 (fn th => disj1_tac >> ACCEPT_TAC th) strip_assume_tac) >>
  disj2_tac >> qexistsl [`y`,`u`] >> simp[Abbr `edge`]
QED

Finalise revert_spine_link_rows
