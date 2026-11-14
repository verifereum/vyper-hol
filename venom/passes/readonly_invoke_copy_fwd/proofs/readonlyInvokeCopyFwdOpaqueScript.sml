(* Relational observations hide return-PC tokens and zero-size pointers.
   Source histories keep their actual values and provenance. *)
Theory readonlyInvokeCopyFwdOpaque
Ancestors
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdCalls readonlyInvokeCopyFwdRel
  frameViewFacts frameRel o1LowerDloadOpaque unitShapeDefs
  internalReturnCopyFwdSim taintAgree o1LowerDloadShared o1LowerDloadRelocationKernel
  venomExecSemantics venomState ptrDiscipline finite_map list rich_list indexedLists pred_set words

Definition ricf_retpc_view_def:
  ricf_retpc_view fn s =
    frame_view fn 0w (s with vs_return_pc_token := 0w)
End

Definition ricf_is_zero_prov_def:
  ricf_is_zero_prov p <=> ?b. p = SOME (b,0)
End

Definition ricf_visible_prov_def:
  ricf_visible_prov G = DRESTRICT G {v | ~ricf_is_zero_prov (FLOOKUP G v)}
End

Definition ricf_visible_params_def:
  ricf_visible_params PG = MAP (\p. if ricf_is_zero_prov p then NONE else p) PG
End

Definition ricf_opaque_value_agree_def:
  ricf_opaque_value_agree sites p m x y <=>
    ricf_is_zero_prov p \/ ricf_value_agree sites p m x y
End

Definition ricf_opaque_params_def:
  ricf_opaque_params PG xs =
    MAPi (\j x. if j < LENGTH PG /\ ricf_is_zero_prov (EL j PG) then 0w else x) xs
End

Definition ricf_opaque_view_def:
  ricf_opaque_view fn PG G s = s with <|
    vs_return_pc_token := 0w;
    vs_vars := FMAP_MAP2 (\(v,x).
      if retpc_var fn v \/ ricf_is_zero_prov (FLOOKUP G v) then 0w else x) s.vs_vars;
    vs_params := ricf_opaque_params PG s.vs_params |>
End

Definition ricf_opaque_params_agree_def:
  ricf_opaque_params_agree sites PG xs ys <=>
    LENGTH xs = LENGTH ys /\ LENGTH PG = LENGTH xs /\
    (!j. j < LENGTH xs ==>
      ricf_opaque_value_agree sites (EL j PG) {} (EL j xs) (EL j ys))
End

Definition ricf_opaque_frame_agree_def:
  ricf_opaque_frame_agree fn D X sites PG G tn s t <=>
    ricf_frame_agree D X sites (ricf_visible_params PG) (ricf_visible_prov G) tn
      (ricf_opaque_view fn PG G s) (ricf_opaque_view fn PG G t)
End

Definition ricf_opaque_live_stack_agree_def:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t <=>
    LENGTH maps = LENGTH stk /\ LENGTH targets = LENGTH stk /\
    (!j. j < LENGTH stk ==>
      ricf_opaque_frame_agree (EL j stk).cf_fn D
        (ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk))
        (EL j maps)
        (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
        (EL j stk).cf_prov (tn with t_var := (EL j stk).cf_tvar)
        (merge_callee_state (EL j stk).cf_state s)
        (merge_callee_state (EL j targets) t))
End

Theorem ricf_retpc_view_vars:
  FLOOKUP (ricf_retpc_view fn s).vs_vars x =
    OPTION_MAP (\v. if retpc_var fn x then 0w else v) (FLOOKUP s.vs_vars x)
Proof
  simp[ricf_retpc_view_def, frame_view_vars_lookup]
QED

Theorem ricf_retpc_view_domains[simp]:
  FDOM (ricf_retpc_view fn s).vs_vars = FDOM s.vs_vars
Proof
  simp[ricf_retpc_view_def, frame_view_def, FMAP_MAP2_THM]
QED

Theorem ricf_retpc_view_update_var:
  ricf_retpc_view fn (update_var x v s) =
    update_var x (if retpc_var fn x then 0w else v) (ricf_retpc_view fn s)
Proof
  simp[ricf_retpc_view_def, frame_view_def, update_var_def, FMAP_MAP2_FUPDATE]
QED

Theorem ricf_retpc_view_merge:
  ricf_retpc_view fn (merge_callee_state caller callee) =
    merge_callee_state (ricf_retpc_view fn caller) callee
Proof
  simp[ricf_retpc_view_def, frame_view_def, merge_callee_state_def]
QED

Theorem ricf_retpc_view_index:
  ricf_retpc_view fn (s with vs_inst_idx := k) =
    ricf_retpc_view fn s with vs_inst_idx := k
Proof
  simp[ricf_retpc_view_def, frame_view_def]
QED

Theorem ricf_retpc_view_adopt:
  ricf_retpc_view fn (adopt_return_fmp ret s) =
    adopt_return_fmp ret (ricf_retpc_view fn s)
Proof
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, ricf_retpc_view_def, frame_view_def]
QED

Theorem ricf_retpc_view_cross[simp]:
  ircf_cross tn gam (ricf_retpc_view fn s) (ricf_retpc_view fn t) <=>
    ircf_cross tn gam s t
Proof
  simp[ircf_cross_def, ricf_retpc_view_def, frame_view_def]
QED

Theorem ricf_retpc_view_operand:
  (!x. op = Var x ==> ~retpc_var fn x) ==>
  eval_operand op (ricf_retpc_view fn s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, ricf_retpc_view_vars,
    ricf_retpc_view_def, frame_view_def] >>
  strip_tac >> Cases_on `FLOOKUP s.vs_vars s'` >> simp[]
QED

Theorem ricf_retpc_view_operands:
  !ops. (!x. MEM (Var x) ops ==> ~retpc_var fn x) ==>
    eval_operands ops (ricf_retpc_view fn s) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h (ricf_retpc_view fn s) = eval_operand h s` by
    (irule ricf_retpc_view_operand >> metis_tac[]) >>
  simp[] >> first_x_assum irule >> metis_tac[]
QED

Theorem ricf_visible_prov_lookup[simp]:
  FLOOKUP (ricf_visible_prov G) v =
    if ricf_is_zero_prov (FLOOKUP G v) then NONE else FLOOKUP G v
Proof
  simp[ricf_visible_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `ricf_is_zero_prov (FLOOKUP G v)` >> simp[]
QED

Theorem ricf_visible_prov_set:
  ricf_visible_prov (set_prov G [out] p) =
    set_prov (ricf_visible_prov G) [out]
      (if ricf_is_zero_prov p then NONE else p)
Proof
  simp[fmap_eq_flookup] >> qx_gen_tac `v` >> Cases_on `p` >>
  simp[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `v = out` >> simp[ricf_is_zero_prov_def] >>
  rpt IF_CASES_TAC >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    ricf_is_zero_prov_def]
QED

Theorem ricf_opaque_value_normalized:
  ricf_opaque_value_agree sites p m x y <=>
  ricf_value_agree sites (if ricf_is_zero_prov p then NONE else p) m
    (if ricf_is_zero_prov p then 0w else x)
    (if ricf_is_zero_prov p then 0w else y)
Proof
  Cases_on `ricf_is_zero_prov p` >>
  simp[ricf_opaque_value_agree_def, ricf_value_agree_def,
    ld_value_agree_def, word_agree_except_def]
QED

Theorem ricf_opaque_params_length[simp]:
  LENGTH (ricf_opaque_params PG xs) = LENGTH xs
Proof simp[ricf_opaque_params_def]
QED

Theorem ricf_opaque_params_el:
  j < LENGTH xs ==>
  EL j (ricf_opaque_params PG xs) =
    if j < LENGTH PG /\ ricf_is_zero_prov (EL j PG) then 0w else EL j xs
Proof simp[ricf_opaque_params_def, EL_MAPi]
QED

Theorem ricf_opaque_view_vars:
  FLOOKUP (ricf_opaque_view fn PG G s).vs_vars v =
    OPTION_MAP (\x. if retpc_var fn v \/ ricf_is_zero_prov (FLOOKUP G v)
      then 0w else x) (FLOOKUP s.vs_vars v)
Proof simp[ricf_opaque_view_def, FLOOKUP_FMAP_MAP2]
QED

Theorem ricf_opaque_view_domains[simp]:
  FDOM (ricf_opaque_view fn PG G s).vs_vars = FDOM s.vs_vars
Proof simp[ricf_opaque_view_def, FMAP_MAP2_THM]
QED

Theorem ricf_opaque_view_update_var:
  ricf_opaque_view fn PG (set_prov G [out] p) (update_var out x s) =
    update_var out
      (if retpc_var fn out \/ ricf_is_zero_prov p then 0w else x)
      (ricf_opaque_view fn PG G s)
Proof
  simp[ricf_opaque_view_def, update_var_def, FMAP_MAP2_FUPDATE,
    venom_state_component_equality] >>
  simp[fmap_eq_flookup, FLOOKUP_FMAP_MAP2, FLOOKUP_UPDATE] >>
  qx_gen_tac `v` >> Cases_on `v = out` >>
  Cases_on `p` >> simp[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    ricf_is_zero_prov_def]
QED

Theorem ricf_opaque_view_merge:
  ricf_opaque_view fn PG G (merge_callee_state caller callee) =
    merge_callee_state (ricf_opaque_view fn PG G caller) callee
Proof simp[ricf_opaque_view_def, merge_callee_state_def]
QED

Theorem ricf_opaque_view_index:
  ricf_opaque_view fn PG G (s with vs_inst_idx := k) =
    ricf_opaque_view fn PG G s with vs_inst_idx := k
Proof simp[ricf_opaque_view_def]
QED

Theorem ricf_opaque_view_adopt:
  ricf_opaque_view fn PG G (adopt_return_fmp ret s) =
    adopt_return_fmp ret (ricf_opaque_view fn PG G s)
Proof Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, ricf_opaque_view_def]
QED

Theorem ricf_opaque_view_cross[simp]:
  ircf_cross tn gam (ricf_opaque_view fn PG G s) (ricf_opaque_view fn PG G t) <=>
    ircf_cross tn gam s t
Proof simp[ircf_cross_def, ricf_opaque_view_def]
QED

Definition ricf_retpc_operand_def:
  ricf_retpc_operand fn op <=> ?v. op = Var v /\ retpc_var fn v
End

Theorem ricf_opaque_frame_operand_masked:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
    ricf_opaque_value_agree sites (op_prov G op) (op_taint tn op)
      (if ricf_retpc_operand fn op then 0w else x)
      (if ricf_retpc_operand fn op then 0w else y)
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
    ricf_retpc_operand_def] >> rpt strip_tac
  >- simp[ricf_opaque_value_agree_def, ricf_value_agree_def,
       ld_value_agree_def, word_agree_except_def]
  >- (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
      `?y. FLOOKUP t.vs_vars s' = SOME y` by metis_tac[FLOOKUP_DEF] >>
      `s' IN FDOM s.vs_vars /\ s.vs_vars ' s' = x /\
       t.vs_vars ' s' = y` by fs[FLOOKUP_DEF] >>
      qexists_tac `y` >> simp[] >>
      Cases_on `ricf_is_zero_prov (FLOOKUP G s')` >>
      simp[ricf_opaque_value_agree_def] >>
      qpat_x_assum `!v. v IN _ ==> _` (qspec_then `s'` mp_tac) >>
      simp[ricf_opaque_view_def, FMAP_MAP2_THM, op_taint_def]) >>
  fs[ricf_opaque_frame_agree_def] >>
  drule ricf_frame_agree_normalized >>
  disch_then (mp_tac o MATCH_MP taint_agree_frame) >>
  simp[ricf_opaque_view_def, venom_state_component_equality] >> strip_tac >>
  simp[ricf_opaque_value_agree_def, ricf_value_agree_def,
    ld_value_agree_def, word_agree_except_def]
QED

Theorem ricf_opaque_frame_operand:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
    ricf_opaque_value_agree sites (op_prov G op) (op_taint tn op) x y
Proof
  strip_tac >> drule_all ricf_opaque_frame_operand_masked >>
  fs[ricf_retpc_operand_def] >> metis_tac[]
QED

Theorem ricf_opaque_frame_params:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_params_agree sites PG s.vs_params t.vs_params
Proof
  simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def,
    ricf_params_agree_def, ricf_opaque_params_agree_def,
    ricf_opaque_view_def, ricf_visible_params_def, LENGTH_MAP] >>
  rpt strip_tac >> simp[ricf_opaque_value_normalized] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[EL_MAP, ricf_opaque_params_el]
QED

Theorem ricf_opaque_frame_inst_idx:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG G tn
    (s with vs_inst_idx := k) (t with vs_inst_idx := k)
Proof
  simp[ricf_opaque_frame_agree_def, ricf_opaque_view_index] >>
  metis_tac[ricf_frame_inst_idx]
QED

Theorem ricf_opaque_frame_bind:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  ricf_opaque_value_agree sites p m
    (if retpc_var fn out then 0w else x)
    (if retpc_var fn out then 0w else y) ==>
  ricf_opaque_frame_agree fn D X sites PG (set_prov G [out] p)
    (tn with t_var := set_var_taint tn.t_var [out] m)
    (update_var out x s) (update_var out y t)
Proof
  simp[ricf_opaque_frame_agree_def, ricf_opaque_view_update_var,
    ricf_visible_prov_set, ricf_opaque_value_normalized] >>
  Cases_on `ricf_is_zero_prov p` >> Cases_on `retpc_var fn out` >>
  simp[] >> metis_tac[ricf_frame_agree_update_var]
QED

Theorem ricf_opaque_live_stack_update_var:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t ==>
  ricf_opaque_live_stack_agree D ids (tn with t_var := tv) maps stk targets
    (update_var out x s) (update_var out y t)
Proof
  simp[ricf_opaque_live_stack_agree_def, merge_callee_state_def, update_var_def]
QED

Theorem ricf_opaque_live_stack_empty[simp]:
  ricf_opaque_live_stack_agree D ids tn [] [] [] s t
Proof simp[ricf_opaque_live_stack_agree_def]
QED

Theorem ricf_opaque_view_dead:
  ircf_dead ids (ricf_opaque_view fn PG G s)
    (MAP (\f. f with cf_state := ricf_opaque_view f.cf_fn f.cf_params f.cf_prov f.cf_state) stk) =
  ircf_dead ids s stk
Proof simp[ircf_dead_def, MAP_MAP_o, combinTheory.o_DEF, ricf_opaque_view_def]
QED

Theorem ricf_opaque_complete_params:
  ricf_visible_params (ricf_complete_params PG xs) =
    ricf_complete_params (ricf_visible_params PG) (ricf_opaque_params PG xs)
Proof
  simp[ricf_visible_params_def, ricf_complete_params_def, map_replicate,
    ricf_is_zero_prov_def]
QED

Theorem ricf_opaque_params_complete:
  ricf_opaque_params (ricf_complete_params PG xs) ys = ricf_opaque_params PG ys
Proof
  simp[ricf_opaque_params_def] >> irule MAPi_CONG' >> simp[] >>
  qx_gen_tac `j` >> strip_tac >> Cases_on `j < LENGTH PG`
  >- (`j < LENGTH (ricf_complete_params PG xs)` by
        (simp[ricf_complete_params_def] >> decide_tac) >>
      simp[ricf_complete_params_def, EL_APPEND_EQN]) >>
  Cases_on `j < LENGTH (ricf_complete_params PG xs)` >> simp[] >>
  `j - LENGTH PG < LENGTH xs - LENGTH PG` by
    (fs[ricf_complete_params_def] >> decide_tac) >>
  simp[ricf_complete_params_def, EL_APPEND_EQN, EL_REPLICATE,
    ricf_is_zero_prov_def]
QED

Theorem ricf_opaque_view_complete_params:
  ricf_opaque_view fn (ricf_complete_params PG s.vs_params) G s =
  ricf_opaque_view fn PG G s
Proof
  simp[ricf_opaque_view_def, ricf_opaque_params_def,
    venom_state_component_equality] >>
  irule MAPi_CONG' >> simp[] >>
  qx_gen_tac `j` >> strip_tac >>
  simp[ricf_complete_params_def, EL_APPEND_EQN] >>
  Cases_on `j < LENGTH PG` >> simp[EL_REPLICATE, ricf_is_zero_prov_def]
QED

Theorem ricf_opaque_live_stack_kernel:
  LENGTH targets = LENGTH stk ==>
  (ricf_opaque_live_stack_agree D ids tn maps stk targets s t <=>
   ricf_live_stack_agree D ids tn maps
     (MAP (\f. f with <|
       cf_state := ricf_opaque_view f.cf_fn f.cf_params f.cf_prov f.cf_state;
       cf_prov := ricf_visible_prov f.cf_prov;
       cf_params := ricf_visible_params f.cf_params |>) stk)
     (MAP (\(f,target). ricf_opaque_view f.cf_fn f.cf_params f.cf_prov target)
       (ZIP (stk,targets))) s t)
Proof
  strip_tac >>
  simp[ricf_opaque_live_stack_agree_def, ricf_live_stack_agree_def,
    ricf_opaque_frame_agree_def, LENGTH_ZIP, EL_MAP, EL_ZIP, GSYM MAP_DROP,
    ricf_opaque_view_merge, ricf_opaque_view_dead, ricf_opaque_complete_params,
    ricf_opaque_view_complete_params, ricf_opaque_view_def,
    ricf_opaque_params_complete, ircf_dead_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem ricf_opaque_setup_callee_frame:
  ricf_opaque_frame_agree caller D X oldsites oldPG G tn s t /\
  ricf_opaque_params_agree sites PG args args' /\ ricf_sites_ok sites /\
  ircf_cross tn (ricf_site_triples sites) s t /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_opaque_frame_agree fn D X sites PG FEMPTY
    (tn with t_var := FEMPTY) cs ct
Proof
  Cases_on `NULL fn.fn_blocks` >> simp[setup_callee_def] >>
  rpt strip_tac >> gvs[] >>
  fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def,
     ricf_opaque_view_def, ricf_visible_prov_def, ricf_visible_params_def,
     ricf_opaque_params_agree_def, ricf_params_agree_def,
     taint_agree_def, ld_shared_agree_def, ricf_value_agree_def,
     ld_value_agree_def, word_agree_except_def, ircf_cross_def] >> gvs[] >>
  reverse conj_tac
  >- (rpt strip_tac
      >~ [`EL j (ricf_opaque_params PG args)`]
      >- (qpat_x_assum `!j. j < _ ==> ricf_opaque_value_agree _ _ _ _ _`
            (qspec_then `j` mp_tac) >>
          simp[EL_MAP, ricf_opaque_params_el, ricf_opaque_value_normalized,
            ricf_value_agree_def, ld_value_agree_def, word_agree_except_def]) >>
      qpat_x_assum `!db sb sz k. _`
        (qspecl_then [`db`,`sb`,`sz`,`k`] mp_tac) >> simp[]) >>
  qpat_x_assum `_ = _ with vs_vars := _` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >>
  simp[venom_state_component_equality, FMAP_MAP2_THM]
QED
