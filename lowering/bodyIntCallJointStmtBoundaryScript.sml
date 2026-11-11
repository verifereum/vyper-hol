(* Resource boundaries for the joint statement step. *)
Theory bodyIntCallJointStmtBoundary
Ancestors
  bodyIntCallJointContract exprLoweringProps loweringPosts compileEnv intCallFrame
  stmtSimProps bodyMemoryDefs freshWrites exprSimHyps allocLimits
  bodyIntCallAggregateStoreLanding bodyIntCallSharpReturn valueCopyBytes
  fragGasPath fragGasMode

Theorem intcall_return_buffer_bound:
  intcall_joint_res fp ce env es sa s /\ fp.jc_rb = SOME (bw,cap) ==>
  w2n bw + cap < dimword (:256)
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def] >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >>
     fs[stmt_state_rel_def] >> goal_assum (drule_at Any)) >>
  gvs[return_buf_frame_def] >> decide_tac
QED

Theorem intcall_return_buffer_source_disjoint:
  intcall_frame_ok fp /\ fp.jc_rb = SOME (bw,cap) /\
  a <= p /\ p + k <= a + z /\
  (fp.jc_lo <= a \/
   ?b n. fp.jc_staged b n /\ b <= a /\ a + z <= b + n) ==>
  loweringStateRelDefs$regions_disjoint p k (w2n bw) cap
Proof
  strip_tac >>
  qpat_x_assum `intcall_frame_ok fp` mp_tac >>
  simp[intcall_frame_ok_def] >> strip_tac >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_x_assum `!b z. fp.jc_staged b z ==> _ \/ _` drule >>
  strip_tac >> decide_tac
QED

Theorem intcall_joint_res_next_var:
  intcall_joint_res fp ce env es sa s /\
  sa.cs_next_var <= sb.cs_next_var ==>
  intcall_joint_res fp ce env es sb s
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def] >> strip_tac >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok ce sb s` by
    (drule ret_pc_ok_frame >> disch_then irule >> simp[]) >>
  `return_buf_frame fp.jc_rb ce sb s` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  simp[] >> rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem intcall_type_alloc_headroom:
  expr_sim_inv ce cx env es /\ type_alloc_ok ce ty /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  gvs[type_alloc_ok_def, wordsTheory.dimword_def] >> decide_tac
QED

Theorem intcall_copy_metadata:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es ==>
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv)
Proof
  strip_tac >>
  reverse (rpt conj_tac)
  >- (rpt strip_tac >> drule_all expr_sim_inv_memory_size >> simp[]) >>
  fs[bodySimTheory.body_inv_def, exprSimHypsDefsTheory.expr_sim_inv_def]
QED

Theorem arg_type_fits_antisym:
  (!t u. arg_type_fits t u /\ arg_type_fits u t ==> t = u) /\
  (!ts us. arg_types_fit ts us /\ arg_types_fit us ts ==> ts = us)
Proof
  ho_match_mp_tac vyperTypeSystemTheory.arg_type_fits_ind >>
  rpt conj_tac >>
  simp[Once vyperTypeSystemTheory.arg_type_fits_def] >>
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once vyperTypeSystemTheory.arg_type_fits_def] >>
  strip_tac >> fs[]
QED

Theorem type_widens_to_antisym:
  type_widens_to tenv t u /\ type_widens_to tenv u t ==> t = u
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def] >>
  metis_tac[cj 1 arg_type_fits_antisym]
QED

Theorem intcall_widening_sandwich_headroom:
  expr_sim_inv ce cx env es /\ type_alloc_ok ce a /\
  ~is_word_type p /\ evaluate_type (get_tenv cx) p = SOME tv /\
  type_widens_to (get_tenv cx) p a /\
  type_widens_to (get_tenv cx) a p ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >>
  `p = a` by metis_tac[type_widens_to_antisym] >> gvs[] >>
  drule_all intcall_type_alloc_headroom >> simp[]
QED

(* The physical compiler source may differ from both typed bytestring views.
   Only the small view needs headroom; the write window fits the declared one. *)
Theorem protected_bytestring_store_ret_path:
  compile_store_memory ce src dst declared physical sa = ((),sm) /\
  is_bytestring_type declared /\ is_bytestring_type a /\
  evaluate_type tenv a = SOME av /\
  evaluate_type tenv declared = SOME dv /\
  value_has_type av v /\ value_has_type dv v /\
  val_in_memory av v (w2n sw) s.vs_memory /\
  type_memory_bytes ce a = type_memory_size av /\
  type_memory_size av + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME bw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (!b sz. P b sz ==>
     regions_disjoint b sz (w2n bw) (type_memory_size dv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (?pc. eval_operand rpc s = SOME pc) ==>
  ?n ir u. gas_path ctx func s n (IntRet ir u) /\
    (!b sz. P b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `~is_word_type declared /\ ~is_word_type a` by
    metis_tac[is_bytestring_word_type] >>
  `compile_store_memory ce src dst a declared sa = ((),sm)` by
    gvs[contextTheory.compile_store_memory_def] >>
  `val_in_memory dv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  `!b sz. P b sz ==> regions_disjoint b sz (w2n bw)
     (MIN (type_memory_size dv) (type_memory_size av))` by
    (gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[arithmeticTheory.MIN_DEF]) >>
  `!x. reserved (Var x) \/ Var x = rpc ==> not_fresh_at sa x` by
    metis_tac[] >>
  SUBGOAL_THEN ``a = declared \/
    is_bytestring_type a /\ is_bytestring_type declared`` assume_tac
  >- simp[] >>
  `(if is_word_type declared then sw = typed_val_to_w256 dv v
    else val_in_memory dv v (w2n sw) s.vs_memory)` by simp[] >>
  drule_all (SRULE [] (Q.INST
    [`reserved` |-> `\op. reserved op \/ op = rpc`]
    protected_compatible_store_landing)) >>
  disch_then (qspecl_then [`[]`, `ctx`] strip_assume_tac) >>
  `eval_operand rpc u = SOME pc` by metis_tac[] >>
  `gas_path ctx func u 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u)` by
    (irule emitted_memory_ret_path >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `gas_path ctx func s 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u)` by
    (drule gas_marked_path_exec >> strip_tac >>
     drule_all gas_path_then >> simp[]) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem arg_type_fits_trans:
  (!t u. arg_type_fits t u ==> !v.
    arg_type_fits u v ==> arg_type_fits t v) /\
  (!ts us. arg_types_fit ts us ==> !vs.
    arg_types_fit us vs ==> arg_types_fit ts vs)
Proof
  ho_match_mp_tac vyperTypeSystemTheory.arg_type_fits_ind >>
  rpt conj_tac >>
  simp[Once vyperTypeSystemTheory.arg_type_fits_def] >>
  rpt strip_tac
  >~ [`arg_types_fit (t::ts) vs`]
    >- (Cases_on `vs` >>
        gvs[Once vyperTypeSystemTheory.arg_type_fits_def] >>
        simp[Once vyperTypeSystemTheory.arg_type_fits_def]) >>
  Cases_on `v` >>
  gvs[Once vyperTypeSystemTheory.arg_type_fits_def] >>
  all_tac
  >~ [`arg_type_fits (BaseT (StringT n)) (BaseT b)`]
    >- (Cases_on `b` >> gvs[vyperTypeSystemTheory.arg_type_fits_def])
  >~ [`arg_type_fits (BaseT (BytesT (Dynamic n))) (BaseT b)`]
    >- (Cases_on `b` >> gvs[Once vyperTypeSystemTheory.arg_type_fits_def] >>
        rename1 `arg_type_fits _ (BaseT (BytesT bd))` >> Cases_on `bd` >>
        gvs[vyperTypeSystemTheory.arg_type_fits_def]) >>
  all_tac
  >~ [`arg_type_fits (ArrayT _ (Dynamic _)) (ArrayT elem bd)`]
    >- (Cases_on `bd` >>
        gvs[Once vyperTypeSystemTheory.arg_type_fits_def] >>
        simp[Once vyperTypeSystemTheory.arg_type_fits_def])
  >~ [`arg_type_fits (ArrayT _ (Fixed _)) (ArrayT elem bd)`]
    >- (Cases_on `bd` >>
        gvs[Once vyperTypeSystemTheory.arg_type_fits_def] >>
        simp[Once vyperTypeSystemTheory.arg_type_fits_def]) >>
  simp[Once vyperTypeSystemTheory.arg_type_fits_def]
QED

Theorem type_widens_to_trans:
  type_widens_to tenv t u /\ type_widens_to tenv u v ==>
  type_widens_to tenv t v
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def] >>
  metis_tac[cj 1 arg_type_fits_trans]
QED
