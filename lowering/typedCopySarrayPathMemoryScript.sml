(* Compiler-facing finite paths for slow fixed-array typed copies. *)
Theory typedCopySarrayPathMemory
Ancestors typedCopyArrayInitMemory typedCopyLoopPlacementMemory
  typedCopyArrayLoopMemory typedMemoryCopy exprOperandVar exprLoweringProps
  fragExecMem fragGasPathMem venomExecSemantics venomState
  ASCIInumbers words list arithmetic

Theorem typed_copy_sarray_slow_path_mem:
  ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
    ~is_abi_dynamic ce.ce_struct_fields dty) /\
  compile_copy_sarray_typed ce dst dty src sty N sa = ((),sz) /\
  fn_has_code sa sz func /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
    (w2n sw + i * type_memory_size stv) s.vs_memory /\
    val_wf stv (f i) /\ val_wf dtv (f i)) /\
  N < dimword (:256) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  w2n sw + N * type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + N * type_memory_size dtv <= s.vs_alloca_next /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!i cd cs a b u pw qw.
    i < N /\ compile_store_memory_typed ce cd dty cs sty a = ((),b) /\
    fn_has_code a b func /\
    (!x. cs = Var x \/ cd = Var x ==> not_fresh_at a x) /\
    eval_operand cs u = SOME pw /\ eval_operand cd u = SOME qw /\
    val_in_memory stv (f i) (w2n pw) u.vs_memory /\
    w2n pw + type_memory_size stv < dimword (:256) /\
    w2n qw + type_memory_size dtv < dimword (:256) /\
    (w2n pw + type_memory_size stv <= w2n qw \/
     w2n qw + type_memory_size dtv <= w2n pw) /\
    w2n pw + type_memory_size stv <= u.vs_alloca_next /\
    w2n qw + type_memory_size dtv <= u.vs_alloca_next /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts /\ ~u.vs_halted ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\
      val_in_memory dtv (f i) (w2n qw) v.vs_memory /\
      typed_copy_state_frame a (w2n qw) (type_memory_size dtv) u v /\
      v.vs_current_bb = b.cs_current_bb /\
      v.vs_inst_idx = LENGTH b.cs_current_insts /\ ~v.vs_halted) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_index_inv sa ("%" ++ toString sa.cs_next_var)
      src dst sw dw f stv dtv N s N t /\
    t.vs_current_bb = sz.cs_current_bb /\
    t.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~t.vs_halted /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule_all typed_copy_sarray_loop_placement >> strip_tac >>
  rename1 `si.cs_current_bb = body_lbl` >>
  `!i. i < N ==> val_in_memory stv (f i)
    (w2n sw + i * type_memory_size stv) s.vs_memory` by metis_tac[] >>
  drule_all typed_copy_sarray_header_init_path_mem >>
  disch_then (qspecl_then [`ctx`, `dtv`] mp_tac) >>
  simp[] >> strip_tac >>
  `!j u. j < N /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s j u /\
    eval_operand (Var sp) u = SOME (sw + n2w (j * type_memory_size stv)) /\
    eval_operand (Var dp) u = SOME (dw + n2w (j * type_memory_size dtv)) /\
    u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 4 /\ ~u.vs_halted ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\
      typed_copy_state_frame sc (w2n dw + j * type_memory_size dtv)
        (type_memory_size dtv) u v /\
      val_in_memory dtv (f j) (w2n dw + j * type_memory_size dtv) v.vs_memory /\
      v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\ ~v.vs_halted` by
    (rpt strip_tac >> suspend "child") >>
  `!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)` by metis_tac[] >>
  `?v. gas_path_mem ctx func t 0 (OK v) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s N v /\
    v.vs_current_bb = exit /\ v.vs_inst_idx = 0 /\ ~v.vs_halted /\
    v.vs_alloca_next = t.vs_alloca_next` by
    (irule typed_copy_array_loop_path_mem >>
     asm_simp_tac (srw_ss()) [] >>
     conj_tac >- gvs[] >> conj_tac
     >- (qexistsl_tac [`sc`, `sc.cs_next_id + 3`, `back`, `bb`,
           `se.cs_next_id`, `body_lbl`, `doff`, `done`, `dp`,
           `se.cs_current_bb`, `sc.cs_next_id`, `lt`, `se.cs_current_insts`,
           `so`, `sp`, `test`, `"%" ++ toString se.cs_next_var`] >> gvs[] >> metis_tac[]) >>
     qexists_tac `0` >> simp[]) >>
  qexists_tac `v` >> gvs[] >>
  drule_all gas_path_mem_then >> simp[]
QED

Resume typed_copy_sarray_slow_path_mem[child]:
  markerLib.RESUME_TAC >> (
  `w2n sw + j * type_memory_size stv + type_memory_size stv <=
     w2n sw + N * type_memory_size stv /\
   w2n dw + j * type_memory_size dtv + type_memory_size dtv <=
     w2n dw + N * type_memory_size dtv` by
    metis_tac[typed_copy_array_subinterval] >>
  `w2n (sw + n2w (j * type_memory_size stv)) =
     w2n sw + j * type_memory_size stv /\
   w2n (dw + n2w (j * type_memory_size dtv)) =
     w2n dw + j * type_memory_size dtv` by
    (conj_tac >> irule typed_copy_offset_nonwrap >> decide_tac) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_index_inv_def, typed_copy_state_frame_def,
        venom_state_component_equality] >>
  qpat_x_assum `!i cd cs a b u pw qw. _` (qspec_then `j` mp_tac) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`u`, `sw + n2w (j * type_memory_size stv)`,
    `dw + n2w (j * type_memory_size dtv)`] mp_tac) >>
  impl_tac
  >- (gvs[typed_copy_index_inv_def] >> metis_tac[]) >>
  disch_then strip_assume_tac >> qexists_tac `v` >> simp[] >>
  metis_tac[typed_copy_state_frame_mono])
QED

Finalise typed_copy_sarray_slow_path_mem
