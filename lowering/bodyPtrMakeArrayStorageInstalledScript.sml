(* Install the actual compiler certificate around the counted loop invariant. *)
Theory bodyPtrMakeArrayStorageInstalled
Ancestors
  bodyPtrMakeArrayStorageLoop bodyPtrMakeArrayStorageSuccessor
  bodyPtrMakeArrayStorageControl bodyPtrMakeArrayStorageEndpoints
  exprSimStorageCopy exprSimCopy exprLoweringProps emitHelperProps
  fragExec fragGasPathPtr venomState venomInst ptrDiscipline bodyPtrDefs
  finite_map pred_set rich_list list words

Theorem storage_copy_prefix_exterior:
  copy_prefix loc a b n sbase k s ==>
  mem_agree_outside {i | b <= i /\ i < b+32*n} s.vs_memory sbase.vs_memory
Proof
  simp[copy_prefix_def, mem_agree_outside_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem compile_storage_copy_ptr_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src (Var dst) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  copy_old_operand sa src /\ not_fresh_at sa dst /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  allocas_from 0 s /\ ~s.vs_halted /\ b+32*n < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_prefix loc a b n s n t /\ copy_static t = copy_static s /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    mem_agree_outside {i | b <= i /\ i < b+32*n} t.vs_memory s.vs_memory /\
    ptr_covers H tm dst t (32*n) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i j. i < n /\ j < 32 /\ b+32*i+j IN tm.t_mem ==>
      j IN key_taint (if loc = LocStorage then tn.t_stor else tn.t_trans) (a+n2w i)) /\
    (!i. i < b \/ b+32*n <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_storage_copy_certificate >> strip_tac >>
  drule_all storage_control_layout >> strip_tac >>
  `n < dimword(:256)` by decide_tac >>
  `cv IN {cv;tv;sv;vv;mv;dv;nv} /\ tv IN {cv;tv;sv;vv;mv;dv;nv} /\
   tv <> cv /\ dst NOTIN {cv;tv;sv;vv;mv;dv;nv} /\
   (!x. src = Var x ==> x NOTIN {cv;tv;sv;vv;mv;dv;nv})` by
    (gvs[ALL_DISTINCT, copy_old_operand_def] >> metis_tac[]) >>
  suspend "install"
QED
Resume compile_storage_copy_ptr_path[install]:
  `ste.cs_current_bb = loop_body /\ LENGTH ste.cs_current_insts = 7` by
    gvs[same_blocks_def, emitted_insts_def] >>
  `ste.cs_current_bb = stb.cs_current_bb /\
   ste.cs_current_insts = stb.cs_current_insts ++ emitted_insts stb ste` by
    gvs[same_blocks_def, emitted_insts_def] >>
  qspecl_then [`stb`, `ste`, `fn`, `emitted_insts stb ste`] mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `!j H tm t.
    j < n /\ t.vs_current_bb = loop_body /\ t.vs_inst_idx = 0 /\
    storage_body_inv src dst cv {cv;tv;sv;vv;mv;dv;nv} loc a b n G tn s j H tm t ==>
    ?u J tu. gas_path_ptr D 0 ctx fn PG H tm t 0 J tu (OK u) /\
      storage_body_inv src dst cv {cv;tv;sv;vv;mv;dv;nv} loc a b n G tn s (j+1) J tu u /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `emit_inst JMP _ [] s0 = _` kall_tac >>
     `lookup_block loop_body fn.fn_blocks = SOME bb /\
      ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
      {cv;sv;vv;mv;dv;nv} SUBSET {cv;tv;sv;vv;mv;dv;nv}` by gvs[ALL_DISTINCT, SUBSET_DEF] >>
     qpat_x_assum `!i. i < LENGTH _ ==> _` mp_tac >> simp[] >> disch_tac >>
     drule_all storage_loop_body_backedge >>
     disch_then (qspecl_then [`PG`, `D`] ACCEPT_TAC)) >>
  suspend "iterate"
QED
Resume compile_storage_copy_ptr_path[iterate]:
  drule_all storage_control_init >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  `storage_body_inv src dst cv {cv;tv;sv;vv;mv;dv;nv} loc a b n G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (jump_to hdr (update_var cv 0w s))` by
    (irule storage_loop_init_inv >> simp[]) >>
  qpat_assum `!j H tm t. _` (mp_then Any mp_tac storage_loop_iterate) >>
  disch_then (fn th => qpat_assum `emitted_insts sth stj = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_inst JNZ _ [] stj = _` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`0`, `DRESTRICT G (COMPL {cv})`,
    `tn with t_var := tn.t_var |+ (cv,{})`, `jump_to hdr (update_var cv 0w s)`] mp_tac) >>
  impl_tac >- simp[jump_to_def] >>
  disch_then (qx_choose_then `sf` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qexistsl_tac [`sf`, `Gf`, `tf`] >>
  conj_tac >- suspend "path" >>
  suspend "post"
QED
Resume compile_storage_copy_ptr_path[path]:
  drule_all gas_path_ptr_then >> simp[]
QED
Resume compile_storage_copy_ptr_path[post]:
  `mem_agree_outside {i | b <= i /\ i < b+32*n} sf.vs_memory s.vs_memory` by
    (irule storage_copy_prefix_exterior >> metis_tac[storage_body_inv_prefix]) >>
  gvs[storage_body_inv_def, storage_body_frame_def] >> metis_tac[]
QED
Finalise compile_storage_copy_ptr_path

(* Zero words still executes the installed initialization and test, but no
   source access or destination coverage is required. *)
Theorem compile_storage_copy_zero_ptr_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src (Var dst) 0 loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\ copy_static t = copy_static s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_storage_copy_certificate >> strip_tac >>
  drule_all storage_control_layout >> strip_tac >>
  drule_all storage_control_zero_path >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  qexistsl_tac [`jump_to exit (update_var tv 1w (jump_to hdr (update_var cv 0w s)))`,
    `DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {tv})`,
    `tn with t_var := (tn.t_var |+ (cv,{})) |+ (tv,{})`] >>
  simp[] >>
  simp[jump_to_def, update_var_def, copy_static_def, lookup_var_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_prov_def, op_taint_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]
QED
