(* Composition of the installed storage/transient copy body. *)
Theory bodyPtrMakeArrayStorageSuccessor
Ancestors
  bodyPtrMakeArrayStorageEndpoints fragGasPathPtr exprSimStorageCopy
  venomState venomInst ptrDiscipline bodyPtrDefs pred_set words list

Theorem storage_body_frame_register:
  storage_body_frame writes G tn s H tm t /\ x NOTIN writes ==>
  lookup_var x t = lookup_var x s /\
  op_prov H (Var x) = op_prov G (Var x) /\
  op_taint tm (Var x) = op_taint tn (Var x)
Proof
  simp[storage_body_frame_def]
QED

Theorem storage_body_frame_static:
  storage_body_frame writes G tn s H tm t ==>
  copy_static t = copy_static s /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  allocas_from 0 t = allocas_from 0 s
Proof
  simp[storage_body_frame_def] >> rpt strip_tac >>
  drule copy_static_fields >> simp[allocas_from_def]
QED

Theorem storage_copy_body_ptr_step:
  (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ allocas_from 0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src;Var cv] [sv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MUL [Var cv;Lit 32w] [mv]) /\
  get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [Var dst;Var mv] [dv]) /\
  get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) MSTORE [Var dv;Var vv] []) /\
  get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
  get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv]) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  dst NOTIN {cv;sv;vv;mv;dv;nv} /\
  (!x. src = Var x ==> x NOTIN {cv;sv;vv;mv;dv;nv}) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  lookup_var cv s = SOME (n2w k) /\ op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
  k < n /\ b+32*n < dimword(:256) ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_frame {cv;sv;vv;mv;dv;nv} G tn s H tm t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+7 /\
    ~t.vs_halted /\ allocas_from 0 t /\
    lookup_var cv t = SOME (n2w (k+1)) /\
    op_prov H (Var cv) = NONE /\ op_taint tm (Var cv) = {} /\
    ptr_covers H tm dst t (32*n) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    mem_agree_outside {i | b <= i /\ i < b+32*n} t.vs_memory s.vs_memory /\
    (!i. i < b \/ b+32*n <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!sbase.
      copy_static s = copy_static sbase /\ copy_prefix loc a b n sbase k s /\
      (!i j. i < k /\ j < 32 /\ b+32*i+j IN tn.t_mem ==>
        j IN key_taint (if loc = LocStorage then tn.t_stor else tn.t_trans) (a+n2w i)) ==>
      copy_prefix loc a b n sbase (k+1) t /\
      (!i j. i < k+1 /\ j < 32 /\ b+32*i+j IN tm.t_mem ==>
        j IN key_taint (if loc = LocStorage then tn.t_stor else tn.t_trans) (a+n2w i)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_body_source_endpoint >>
  disch_then (qspecl_then [`PG`, `G`, `D`]
    (qx_choose_then `sl` (qx_choose_then `Gl` (qx_choose_then `tl` strip_assume_tac)))) >>
  `lookup_var cv sl = SOME (n2w k) /\ op_prov Gl (Var cv) = NONE /\
   op_taint tl (Var cv) = {}` by
    (drule storage_body_frame_register >> disch_then (qspec_then `cv` mp_tac) >>
     gvs[ALL_DISTINCT]) >>
  `lookup_var dst sl = SOME (n2w b)` by
    (drule storage_body_frame_register >> disch_then (qspec_then `dst` mp_tac) >>
     gvs[]) >>
  `ptr_covers Gl tl dst sl (32*n)` by
    (drule storage_body_frame_covers >>
     disch_then (qspecl_then [`dst`, `32*n`] mp_tac) >> gvs[]) >>
  `lookup_block sl.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb sl.vs_inst_idx = SOME (mk_inst (id+2) MUL [Var cv;Lit 32w] [mv]) /\
   get_instruction bb (SUC sl.vs_inst_idx) = SOME (mk_inst (id+3) ADD [Var dst;Var mv] [dv]) /\
   mv <> dst /\ dv <> dst` by gvs[arithmeticTheory.ADD1] >>
  drule_all storage_body_destination_stage >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `sd` (qx_choose_then `Gd` (qx_choose_then `td` strip_assume_tac)))) >>
  `lookup_var vv sd = SOME (copy_runtime_word loc s (a+n2w k)) /\
   op_taint td (Var vv) = key_taint
     (if loc = LocStorage then tn.t_stor else tn.t_trans) (a+n2w k)` by
    (drule storage_body_frame_register >> disch_then (qspec_then `vv` mp_tac) >>
     gvs[ALL_DISTINCT]) >>
  `lookup_var cv sd = SOME (n2w k) /\ op_prov Gd (Var cv) = NONE /\
   op_taint td (Var cv) = {}` by
    (drule storage_body_frame_register >> disch_then (qspec_then `cv` mp_tac) >>
     gvs[ALL_DISTINCT]) >>
  `lookup_block sd.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb sd.vs_inst_idx = SOME (mk_inst (id+4) MSTORE [Var dv;Var vv] []) /\
   eval_operand (Var vv) sd = SOME (copy_runtime_word loc s (a+n2w k)) /\
   b+32*k < dimword(:256) /\
   (!j. j IN op_taint td (Var vv) ==> j < 32)` by
    (gvs[eval_operand_def, key_taint_def] >> decide_tac) >>
  drule_all storage_body_store_stage >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `ss` (qx_choose_then `Gs` (qx_choose_then `ts` strip_assume_tac)))) >>
  suspend "counter"
QED

Resume storage_copy_body_ptr_step[counter]:
  `lookup_var cv ss = SOME (n2w k) /\ op_prov Gs (Var cv) = NONE /\
   op_taint ts (Var cv) = {}` by
    (drule storage_body_frame_register >> disch_then (qspec_then `cv` mp_tac) >>
     gvs[]) >>
  `lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb ss.vs_inst_idx = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
   get_instruction bb (SUC ss.vs_inst_idx) = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv])` by
    gvs[arithmeticTheory.ADD1] >>
  drule_all storage_body_counter_stage >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `sf` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)))) >>
  qexistsl_tac [`sf`, `Gf`, `tf`] >>
  conj_tac >- suspend "path" >>
  conj_asm1_tac >- suspend "frame" >>
  conj_tac >- gvs[] >> conj_tac >- gvs[arithmeticTheory.ADD1] >>
  conj_tac >- simp[] >> conj_tac >- suspend "allocas" >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- suspend "coverage" >>
  conj_tac >- gvs[] >> conj_tac >- suspend "exterior" >>
  conj_tac >- suspend "taint_exterior" >>
  suspend "prefix"
QED

Resume storage_copy_body_ptr_step[path]:
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`Gl`, `sl`, `tl`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`Gd`, `sd`, `td`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`Gs`, `ss`, `ts`] >> simp[]
QED
Resume storage_copy_body_ptr_step[frame]:
  gvs[storage_body_frame_def] >> metis_tac[]
QED
Resume storage_copy_body_ptr_step[allocas]:
  drule storage_body_frame_static >> simp[]
QED
Resume storage_copy_body_ptr_step[coverage]:
  drule storage_body_frame_covers >>
  disch_then (qspecl_then [`dst`, `32*n`] mp_tac) >> gvs[]
QED
Resume storage_copy_body_ptr_step[exterior]:
  gvs[mem_agree_outside_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> decide_tac
QED
Resume storage_copy_body_ptr_step[prefix]:
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  imp_res_tac storage_body_frame_static >>
  `copy_prefix loc a b n sbase k sd` by
    (irule copy_prefix_transfer >> qexists_tac `s` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!loc' a' n' sbase' keys. _` drule >>
  disch_then (qspec_then `if loc = LocStorage then tn.t_stor else tn.t_trans` mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[copy_runtime_word_static]) >>
  strip_tac >> conj_tac >-
    (irule copy_prefix_transfer >> qexists_tac `ss` >> simp[]) >>
  gvs[]
QED
Resume storage_copy_body_ptr_step[taint_exterior]:
  gvs[] >> rpt strip_tac >>
  qpat_x_assum `!i. i < b + 32 * k \/ _ ==> _` irule >> decide_tac
QED
Finalise storage_copy_body_ptr_step

(* The loop invariant packages the stable frame and the initialized/tainted
   prefix once, so the header/body/exit consumers need not repeat them.
   The PC is intentionally excluded: control edges transport this invariant. *)
Definition storage_body_inv_def:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s <=>
    storage_body_frame writes Gbase tnbase sbase G tn s /\
    eval_operand src s = SOME a /\ op_taint tn src = {} /\
    lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
    lookup_var cv s = SOME (n2w k) /\ op_prov G (Var cv) = NONE /\
    op_taint tn (Var cv) = {} /\ allocas_from 0 s /\ ~s.vs_halted /\
    copy_prefix loc a b n sbase k s /\ LENGTH sbase.vs_memory <= LENGTH s.vs_memory /\
    (!i j. i < k /\ j < 32 /\ b+32*i+j IN tn.t_mem ==>
      j IN key_taint (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) (a+n2w i)) /\
    (!i. i < b \/ b+32*n <= i ==> (i IN tn.t_mem <=> i IN tnbase.t_mem))
End

Theorem storage_body_inv_frame:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  storage_body_frame writes Gbase tnbase sbase G tn s
Proof
  simp[storage_body_inv_def]
QED

Theorem storage_body_inv_prefix:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  copy_prefix loc a b n sbase k s
Proof
  simp[storage_body_inv_def]
QED

Theorem storage_body_frame_operand:
  storage_body_frame writes G tn s H tm t /\
  (!x. op = Var x ==> x NOTIN writes) ==>
  eval_operand op t = eval_operand op s /\
  op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op
Proof
  strip_tac >> drule storage_body_frame_static >> strip_tac >>
  drule copy_static_fields >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def, op_prov_def, op_taint_def,
    storage_body_frame_def] >> metis_tac[]
QED

Theorem storage_copy_body_ptr_successor:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src;Var cv] [sv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MUL [Var cv;Lit 32w] [mv]) /\
  get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [Var dst;Var mv] [dv]) /\
  get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) MSTORE [Var dv;Var vv] []) /\
  get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
  get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv]) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  {cv;sv;vv;mv;dv;nv} SUBSET writes /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) /\
  k < n /\ b+32*n < dimword(:256) /\
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase (k+1) H tm t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+7
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `storage_body_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_body_inv_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `dst NOTIN {cv;sv;vv;mv;dv;nv} /\
   (!x. src = Var x ==> x NOTIN {cv;sv;vv;mv;dv;nv})` by
    (gvs[SUBSET_DEF] >> metis_tac[]) >>
  drule_all storage_copy_body_ptr_step >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `tm` strip_assume_tac)))) >>
  qexistsl_tac [`t`, `H`, `tm`] >> simp[] >>
  `storage_body_frame writes G tn s H tm t` by
    (drule_all storage_body_frame_mono >> simp[]) >>
  `eval_operand src t = SOME a /\ op_taint tm src = {}` by
    (drule storage_body_frame_operand >> disch_then (qspec_then `src` mp_tac) >> simp[]) >>
  `lookup_var dst t = SOME (n2w b)` by
    (drule storage_body_frame_register >> disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
  conj_tac >- (drule_all storage_body_frame_trans >> simp[]) >>
  simp[] >>
  imp_res_tac storage_body_frame_static >>
  qpat_x_assum `!sbase. _` (qspec_then `sbase` mp_tac) >>
  simp[] >> strip_tac >> simp[] >> metis_tac[]
QED
