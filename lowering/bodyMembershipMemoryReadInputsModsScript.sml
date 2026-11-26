(* Normalize the memory representation into the element and header load inputs. *)
Theory bodyMembershipMemoryReadInputsMods
Ancestors
  bodyPtrBopHashFootprint abiDecodeStaticProps builtinProps loweringPosts
  bodyPtrDefs ptrDiscipline compileEnv context venomState vyperValue
  vyperState words finite_map list arithmetic

Theorem membership_covered_offset[local]:
  ptr_mem_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) Gu Tu u /\
  evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME (ArrayTV et pbd) /\
  eval_operand (vv_operand vv) u = SOME w /\
  off + 32 <= type_memory_size (ArrayTV et pbd) /\
  (!off n src dst t G' T'. vv_operand vv = Var src /\
    0 < n /\ off + n <= type_memory_size (ArrayTV et pbd) /\
    lookup_var dst t = SOME (w + n2w off) /\
    FLOOKUP G' dst = FLOOKUP Gu src /\ op_taint T' (Var dst) = {} ==>
    ptr_covers G' T' dst t n) ==>
  (?src. vv_operand vv = Var src) /\
  (!x p Gp Tp. lookup_var x p = SOME (w + n2w off) /\
    FLOOKUP Gp x = op_prov Gu (vv_operand vv) /\ op_taint Tp (Var x) = {} ==>
    ptr_covers Gp Tp x p 32)
Proof
  strip_tac >>
  `val_footprint (ArrayTV et pbd) (ArrayV av) <> 0` by
    (simp[val_footprint_def] >> decide_tac) >>
  drule_all_then strip_assume_tac ptr_mem_ok_bounds >>
  simp[op_prov_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  qexists_tac `off` >> simp[]
QED

Theorem membership_memory_read_inputs_mods:
  elem_size_in_location cenv LocMemory ety = 32 /\
  evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME (ArrayTV et pbd) /\
  u.vs_alloca_next < dimword (:256) /\
  eval_operand (vv_operand vv) u = SOME w /\ op_taint Tu (vv_operand vv) = {} /\
  ptr_mem_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) Gu Tu u /\
  (0 < type_memory_size (ArrayTV et pbd) ==>
    w2n w + type_memory_size (ArrayTV et pbd) <= u.vs_alloca_next) /\
  (!off n src dst t G' T'. vv_operand vv = Var src /\
    0 < n /\ off + n <= type_memory_size (ArrayTV et pbd) /\
    lookup_var dst t = SOME (w + n2w off) /\
    FLOOKUP G' dst = FLOOKUP Gu src /\ op_taint T' (Var dst) = {} ==>
    ptr_covers G' T' dst t n) /\
  (!i. i < LENGTH ws ==>
    (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <=
      type_memory_size (ArrayTV et pbd) /\
    mem_word_taint Tu.t_mem
      (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
    mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u = EL i ws) /\
  (!cap. bd = Dynamic cap ==>
    32 <= type_memory_size (ArrayTV et pbd) /\
    mem_word_taint Tu.t_mem (w2n w) = {} /\ mload (w2n w) u = n2w (LENGTH ws)) ==>
  (!i. i < LENGTH ws ==>
    let skip = case bd of Fixed _ => 0 | Dynamic _ => word_scale LocMemory in
    let addr = w + n2w (skip + elem_size_in_location cenv LocMemory ety * i) in
    ptr_load_val cenv.ce_is_ctor LocMemory addr u = EL i ws /\
    w2n addr + 32 <= u.vs_alloca_next /\ mem_word_taint Tu.t_mem (w2n addr) = {} /\
    !x p Gp Tp. lookup_var x p = SOME addr /\
      FLOOKUP Gp x = op_prov Gu (vv_operand vv) /\ op_taint Tp (Var x) = {} ==>
      ptr_covers Gp Tp x p 32) /\
  (!cap. bd = Dynamic cap ==>
    (?x. vv_operand vv = Var x /\ ptr_covers Gu Tu x u 32) /\
    w2n w + 32 <= u.vs_alloca_next /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
    mload (w2n w) u = n2w (LENGTH ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!i. i < LENGTH ws ==> _` (drule_then strip_assume_tac) >>
      simp_tac bool_ss [LET_THM] >>
      simp[word_scale_def, ptr_load_val_def] >>
      `32 * i = i * 32` by irule MULT_COMM >>
      qabbrev_tac `off = (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32` >>
      `w2n w + off + 32 <= u.vs_alloca_next` by decide_tac >>
      `w2n (w + n2w off) = w2n w + off` by
        (irule w2n_add_n2w_lt >> decide_tac) >>
      `!x p Gp Tp. lookup_var x p = SOME (w + n2w off) /\
        FLOOKUP Gp x = op_prov Gu (vv_operand vv) /\ op_taint Tp (Var x) = {} ==>
        ptr_covers Gp Tp x p 32` by
        (drule_all membership_covered_offset >> simp[]) >>
      `32 * i + (case bd of Fixed _ => 0 | Dynamic _ => 32) = off` by
        (simp_tac bool_ss [Abbr `off`] >>
         qpat_assum `32 * i = i * 32` (fn th => PURE_REWRITE_TAC [th]) >>
         irule ADD_COMM) >>
      `mload (w2n w + off) u = EL i ws /\ mem_word_taint Tu.t_mem (w2n w + off) = {}` by
        (simp_tac bool_ss [Abbr `off`, ADD_ASSOC] >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!cap. bd = Dynamic cap ==> _` (drule_then strip_assume_tac) >>
  `w2n w + 32 <= u.vs_alloca_next` by decide_tac >>
  simp[] >>
  mp_tac (Q.INST [`off` |-> `0`] membership_covered_offset) >>
  impl_tac >- (pure_rewrite_tac[ADD_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[WORD_ADD_0] >> strip_tac >>
  rename1 `vv_operand vv = Var src` >> qexists_tac `src` >> simp[] >>
  first_x_assum irule >> fs[eval_operand_def, op_prov_def, WORD_ADD_0]
QED
