(* Local provenance boundaries; not a reachable-frame coherence theorem. *)
Theory o1LowerDloadGhost
Ancestors
  contextCodegenRel execEquivParamBase venomExecProps o1LowerDloadClosure ptrDiscipline finite_map pointerConfinedDefs venomInst memLocDefs pred_set list

Theorem step_prov_origin:
  MEM inst (fn_insts fn) /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  FLOOKUP (step_prov PG G inst s') v = SOME site ==>
  (FLOOKUP G v = SOME site /\ ~MEM v inst.inst_outputs) \/
  v IN ptr_roots P fn \/
  (MEM v inst.inst_outputs /\
   (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN) /\
   ?u. MEM (Var u) inst.inst_operands /\ FLOOKUP G u = SOME site)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `out_prov PG G inst s'` >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, AllCaseEqs()] >>
  `inst_output inst = SOME h` by simp[inst_output_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (disj1_tac >> simp[ptr_roots_def, alloca_roots_def] >>
      metis_tac[inst_output_def]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (disj1_tac >> simp[ptr_roots_def] >>
      metis_tac[inst_output_def]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[out_prov_def, AllCaseEqs()] >>
      simp[ptr_roots_def] >>
      metis_tac[inst_output_def]) >>
  gvs[out_prov_def, AllCaseEqs()] >>
  metis_tac[first_prov_origin]
QED

Theorem ret_operand_not_pointer:
  ptr_use_ok P pv inst /\ inst.inst_opcode = RET /\
  MEM (Var v) inst.inst_operands ==> v NOTIN pv
Proof
  rw[ptr_use_ok_def, is_pointer_preserving_op_def] >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[mem_write_ops_def, mem_read_ops_def, is_pointer_preserving_op_def]
QED

Theorem ret_operand_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = RET /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  rw[taint_ok_def] >>
  qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `op` mp_tac) >>
  simp[]
QED

Theorem ret_operand_no_provenance:
  ptr_use_ok P (fn_pv P fn) inst /\ inst.inst_opcode = RET /\
  FDOM G SUBSET fn_pv P fn /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  rpt strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  drule_all ret_operand_not_pointer >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem step_prov_support:
  FDOM G SUBSET fn_pv P fn /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  MEM inst (fn_insts fn) ==>
  FDOM (step_prov PG G inst s') SUBSET fn_pv P fn
Proof
  rpt strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
  rename1 `v IN FDOM (step_prov PG G inst s')` >>
  `?site. FLOOKUP (step_prov PG G inst s') v = SOME site` by
    metis_tac[FLOOKUP_DEF, optionTheory.IS_SOME_EXISTS] >>
  drule_all step_prov_origin >> strip_tac
  >- (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) 
  >- metis_tac[ptr_roots_subset_fn_pv, SUBSET_DEF] >>
  `u IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  metis_tac[fn_pv_forward, is_pointer_preserving_op_def]
QED

Theorem phis_prov_support:
  !insts. EVERY (\i. MEM i (fn_insts fn)) insts /\
    FDOM G SUBSET fn_pv P fn ==>
    FDOM (phis_prov prev G insts) SUBSET fn_pv P fn
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phis_prov_def] >>
  `FDOM (phis_prov prev G insts) SUBSET fn_pv P fn` by metis_tac[] >>
  Cases_on `h.inst_outputs` >>
  gvs[set_prov_def, FDOM_DRESTRICT, SUBSET_DEF] >>
  Cases_on `t` >> gvs[set_prov_def, FDOM_DRESTRICT, SUBSET_DEF] >>
  Cases_on `phi_prov prev G h` >>
  gvs[FDOM_DRESTRICT, SUBSET_DEF] >>
  gvs[phi_prov_def, AllCaseEqs()] >>
  rename1 `resolve_phi lbl h.inst_operands = SOME op` >>
  drule resolve_phi_MEM >> strip_tac >>
  Cases_on `op` >> gvs[op_prov_def] >>
  `s IN fn_pv P fn` by (fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `h' IN fn_pv P fn` by
    (irule fn_pv_forward >> qexistsl_tac [`h`, `s`] >>
     simp[is_pointer_preserving_op_def]) >>
  metis_tac[]
QED

Theorem entry_prov_support:
  FDOM G SUBSET fn_pv P fn ==>
  FDOM (entry_prov fn s G) SUBSET fn_pv P fn
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule phis_prov_support >> simp[] >>
  drule lookup_block_MEM >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem invoke_prov_positions:
  ptr_use_ok P (fn_pv P fn) inst /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\ FDOM G SUBSET fn_pv P fn ==>
  !k site. k < LENGTH (MAP (op_prov G) ops) /\
    EL k (MAP (op_prov G) ops) = SOME site ==> k IN P nm
Proof
  simp[ptr_use_ok_def] >> rpt strip_tac >> gvs[] >>
  gvs[EL_MAP] >>
  Cases_on `EL k ops` >> gvs[op_prov_def] >>
  `s IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem active_inst_member[local]:
  active_inst fn inst s ==> MEM inst (fn_insts fn)
Proof
  rw[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
  metis_tac[MEM_EL]
QED

Theorem frame_reachable_prov_support:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  !P. EVERY (fn_ptr_ok P) C.ctx_functions ==>
  MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn /\
  (!k site. k < LENGTH PG /\ EL k PG = SOME site ==> k IN P fn.fn_name) /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions /\
    FDOM f.cf_prov SUBSET fn_pv P f.cf_fn /\
    (!k site. k < LENGTH f.cf_params /\ EL k f.cf_params = SOME site ==>
      k IN P f.cf_fn.fn_name)) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[venomInstTheory.lookup_function_MEM])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      irule step_prov_support >> simp[] >> metis_tac[active_inst_member])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[entry_prov_support])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      imp_res_tac venomInstTheory.lookup_function_MEM >> gvs[] >>
      `ptr_use_ok P (fn_pv P fn) inst` by
        (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[active_inst_member]) >>
      `fn'.fn_name = nm` by
        (fs[lookup_function_def] >> drule venomExecProofsTheory.FIND_P >> simp[]) >>
      drule invoke_prov_positions >> simp[] >>
      disch_then (qspecl_then [`G`, `k`, `site`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  gvs[FDOM_DRESTRICT, SUBSET_DEF]
QED

Theorem frame_reachable_active_inst[local]:
  frame_reachable vs C stk PG G tn fn inst s ==> active_inst fn inst s
Proof
  simp[Once frame_reachable_cases] >> metis_tac[]
QED

Theorem frame_reachable_ret_no_provenance:
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\
  inst.inst_opcode = RET /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  rpt strip_tac >>
  drule frame_reachable_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  irule ret_operand_no_provenance >> simp[] >>
  gvs[EVERY_MEM, fn_ptr_ok_def] >>
  metis_tac[frame_reachable_active_inst, active_inst_member]
QED

(* ===== Dynamic ghosts =====

   A provenance map G against a reference map KA: G has every site of KA,
   and where KA has none, G has none or a dynamic site at or above the
   floor fl.  DALLOCA pointers are untagged: they carry a site in the
   frame provenance and none in the reference. *)

Theorem ld_ghost_first_prov:
  !ops.
    (!v x. FLOOKUP (Ke:(string, num # num) fmap) v = SOME x ==>
           FLOOKUP G v = SOME x) /\
    (!v. FLOOKUP Ke v = NONE ==>
       FLOOKUP G v = NONE \/
       ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) /\
    (!v w. MEM (Var v) ops /\ MEM (Var w) ops /\ v IN FDOM G /\
           w IN FDOM G ==> v = w) ==>
    (!x. first_prov Ke ops = SOME x ==> first_prov G ops = SOME x) /\
    (first_prov Ke ops = NONE ==>
       first_prov G ops = NONE \/
       ?b z. first_prov G ops = SOME (b,z) /\ fl <= b /\
             b + z < dimword (:256))
Proof
  Induct >> simp[first_prov_def] >> rpt gen_tac >> strip_tac >>
  `!v w. MEM (Var v) ops /\ MEM (Var w) ops /\ v IN FDOM G /\
         w IN FDOM G ==> v = w` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `h` >> simp[op_prov_def] >>
  rename1 `FLOOKUP Ke v` >>
  Cases_on `FLOOKUP Ke v` >> simp[]
  >- (`FLOOKUP G v = NONE \/
       ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)`
        by metis_tac[] >>
      pop_assum strip_assume_tac >> simp[] >> rpt strip_tac >>
      drule first_prov_origin >> strip_tac >>
      `FLOOKUP G v' = SOME x` by metis_tac[] >>
      `v' = v` by metis_tac[flookup_thm] >> gvs[]) >>
  rename1 `FLOOKUP Ke v = SOME y` >>
  `FLOOKUP G v = SOME y` by metis_tac[] >> simp[]
QED

Theorem ld_ghost_op_prov:
  (!v x. FLOOKUP (KA:(string, num # num) fmap) v = SOME x ==>
         FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP KA v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  (!x. op_prov KA op = SOME x ==> op_prov G op = SOME x) /\
  (op_prov KA op = NONE ==>
     op_prov G op = NONE \/
     ?b z. op_prov G op = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256))
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def]
QED

Theorem ld_ghost_set_prov:
  (!v x. FLOOKUP (KA:(string, num # num) fmap) v = SOME x ==>
         FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP KA v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) /\
  (!x. p = SOME x ==> q = SOME x) /\
  (p = NONE ==>
     q = NONE \/ ?b z. q = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  (!v x. FLOOKUP (set_prov KA outs p) v = SOME x ==>
         FLOOKUP (set_prov G outs q) v = SOME x) /\
  (!v. FLOOKUP (set_prov KA outs p) v = NONE ==>
     FLOOKUP (set_prov G outs q) v = NONE \/
     ?b z. FLOOKUP (set_prov G outs q) v = SOME (b,z) /\ fl <= b /\
           b + z < dimword (:256))
Proof
  strip_tac >> Cases_on `outs`
  >- (simp[set_prov_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `t`
  >- (Cases_on `p` >> Cases_on `q` >>
      gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      rw[] >> gvs[] >> metis_tac[]) >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[set_prov_def, FLOOKUP_DRESTRICT] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem ld_ghost_phis_prov:
  !is.
  (!v x. FLOOKUP (KA:(string, num # num) fmap) v = SOME x ==>
         FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP KA v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  (!v x. FLOOKUP (phis_prov prev KA is) v = SOME x ==>
         FLOOKUP (phis_prov prev G is) v = SOME x) /\
  (!v. FLOOKUP (phis_prov prev KA is) v = NONE ==>
     FLOOKUP (phis_prov prev G is) v = NONE \/
     ?b z. FLOOKUP (phis_prov prev G is) v = SOME (b,z) /\ fl <= b /\
           b + z < dimword (:256))
Proof
  Induct >- simp[phis_prov_def] >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[phis_prov_def] >>
  Cases_on `h.inst_opcode = PHI` >> asm_rewrite_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  irule ld_ghost_set_prov >> simp[] >>
  Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x h.inst_operands` >> simp[] >>
  irule ld_ghost_op_prov >> metis_tac[]
QED

Theorem ld_ghost_entry_prov:
  (!v x. FLOOKUP (KA:(string, num # num) fmap) v = SOME x ==>
         FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP KA v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) ==>
  (!v x. FLOOKUP (entry_prov fn s KA) v = SOME x ==>
         FLOOKUP (entry_prov fn s G) v = SOME x) /\
  (!v. FLOOKUP (entry_prov fn s KA) v = NONE ==>
     FLOOKUP (entry_prov fn s G) v = NONE \/
     ?b z. FLOOKUP (entry_prov fn s G) v = SOME (b,z) /\ fl <= b /\
           b + z < dimword (:256))
Proof
  strip_tac >> simp[entry_prov_def] >>
  CASE_TAC >> simp[] >>
  irule ld_ghost_phis_prov >> metis_tac[]
QED

(* Output provenance away from DALLOCA: the frame provenance keeps every
   reference site, given that pointer arithmetic sees one pointer. *)
Theorem ld_ghost_out_prov:
  (!v x. FLOOKUP (KA:(string, num # num) fmap) v = SOME x ==>
         FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP KA v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)) /\
  LIST_REL (\p q. (!x. p = SOME x ==> q = SOME x) /\
    (p = NONE ==>
       q = NONE \/ ?b z. q = SOME (b,z) /\ fl <= b /\ b + z < dimword (:256)))
    PK PG /\
  inst.inst_opcode <> DALLOCA /\
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
    inst.inst_opcode = ASSIGN) ==>
   !v w. MEM (Var v) inst.inst_operands /\ MEM (Var w) inst.inst_operands /\
         v IN FDOM G /\ w IN FDOM G ==> v = w) ==>
  (!x. out_prov PK KA inst s = SOME x ==> out_prov PG G inst s = SOME x) /\
  (out_prov PK KA inst s = NONE ==>
     out_prov PG G inst s = NONE \/
     ?b z. out_prov PG G inst s = SOME (b,z) /\ fl <= b /\
           b + z < dimword (:256))
Proof
  strip_tac >> simp[out_prov_def] >>
  Cases_on `inst.inst_opcode = ALLOCA` >- simp[] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (fs[LIST_REL_EL_EQN] >>
      Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `t` >> simp[] >>
      Cases_on `h` >> simp[] >>
      rename1 `w2n idx < _` >>
      IF_CASES_TAC >> simp[]) >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN` >> simp[] >>
  irule ld_ghost_first_prov >> metis_tac[]
QED
