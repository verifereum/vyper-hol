(* Concrete loop-address construction shared by compatibility/frame contracts. *)
structure typedCopyLoopAmbientLib =
struct
open HolKernel boolLib bossLib
open venomStateTheory venomInstTheory contextTheory compileEnvTheory
     finite_mapTheory wordsTheory bodyPtrDefsTheory ptrDisciplineTheory
     typedCopyPtrTheory

val address_witnesses =
  rpt gen_tac >> strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  qabbrev_tac `s1 = (update_var so (n2w (i*ss)) s) with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var doff (n2w (i*ds)) s1) with
    vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `t3 = update_var sp (a+n2w (i*ss)) s2` >>
  qabbrev_tac `s3 = t3 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `t4 = update_var dp (b+n2w (i*ds)) s3` >>
  qabbrev_tac `s4 = t4 with vs_inst_idx := SUC s3.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {so})` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {doff})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (so,{})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (doff,{})` >>
  qabbrev_tac `g3 = step_prov PG g2 (mk_inst (id+2) ADD [Var sr;Var so] [sp]) t3` >>
  qabbrev_tac `tn3 = step_taint (mk_inst (id+2) ADD [Var sr;Var so] [sp]) s2 t3 tn2` >>
  qabbrev_tac `g4 = step_prov PG g3 (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) t4` >>
  qabbrev_tac `tn4 = step_taint (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) s3 t4 tn3` >>
  qexistsl_tac [`g4`,`tn4`,`s4`];

fun address_fragment mul_fragment =
  qabbrev_tac `c1 = sb with cs_current_insts := sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so]]` >>
  qabbrev_tac `c2 = sb with cs_current_insts := sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff]]` >>
  qabbrev_tac `c3 = sb with cs_current_insts := sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [Var sr;Var so] [sp]]` >>
  `frag_exec_ptr cx ctx PG sb c1
     (\g t v. g=G /\ t=tn /\ v=s)
     (\g t v. g=g1 /\ t=tn1 /\ v=s1) R` by
    (irule mul_fragment >>
     simp[Abbr `c1`, Abbr `g1`, Abbr `tn1`, Abbr `s1`] >>
     qexistsl_tac [`id`, `Var ctr`, `so`, `Lit (n2w ss)`] >>
     simp[eval_operand_def, word_mul_n2w, op_taint_def]) >>
  `frag_exec_ptr cx ctx PG c1 c2
     (\g t v. g=g1 /\ t=tn1 /\ v=s1)
     (\g t v. g=g2 /\ t=tn2 /\ v=s2) R` by
    (irule mul_fragment >>
     simp[Abbr `c1`, Abbr `c2`, listTheory.APPEND_ASSOC,
          Abbr `g2`, Abbr `tn2`, Abbr `s2`] >>
     qexistsl_tac [`id+1`, `Var ctr`, `doff`, `Lit (n2w ds)`] >>
     gvs[Abbr `s1`, Abbr `tn1`, eval_operand_def, word_mul_n2w,
          op_taint_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `op_taint tn (Var sr) = {} /\ op_taint tn (Var dr) = {}` by
    gvs[ptr_covers_def] >>
  `frag_exec_ptr cx ctx PG c2 c3
     (\g t v. g=g2 /\ t=tn2 /\ v=s2)
     (\g t v. g=g3 /\ t=tn3 /\ v=s3) R` by
    (irule copy_len_binop_frag_ptr >>
     simp[Abbr `c2`, Abbr `c3`, listTheory.APPEND_ASSOC, mk_inst_def] >>
     simp[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `t3`, mk_inst_def] >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `tn2`, Abbr `tn1`,
         eval_operand_def, op_taint_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `frag_exec_ptr cx ctx PG c3 si
     (\g t v. g=g3 /\ t=tn3 /\ v=s3)
     (\g t v. g=g4 /\ t=tn4 /\ v=s4) R` by
    (irule copy_len_binop_frag_ptr >>
     simp[Abbr `c3`, listTheory.APPEND_ASSOC, mk_inst_def] >>
     simp[Abbr `g4`, Abbr `tn4`, Abbr `s4`, Abbr `t4`, mk_inst_def] >>
     simp[Abbr `tn3`, Abbr `t3`, copy_len_binop_ghost_frame] >>
     gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`,
         Abbr `tn2`, Abbr `tn1`, eval_operand_def,
         op_taint_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `cs_extends sb c1 /\ cs_extends c1 c2 /\
   cs_extends c2 c3 /\ cs_extends c3 si` by
    (simp[Abbr `c1`, Abbr `c2`, Abbr `c3`, cs_extends_def,
          listTheory.APPEND_ASSOC]) >>
  `cs_extends c1 si /\ cs_extends c2 si /\ cs_extends sb c3` by
    (simp[Abbr `c1`, Abbr `c2`, Abbr `c3`,
          cs_extends_def, listTheory.APPEND_ASSOC] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[listTheory.APPEND_ASSOC]) >>
  irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qexistsl_tac [`\g t v. g=g1 /\ t=tn1 /\ v=s1`, `c1`] >> simp[] >>
  irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qexistsl_tac [`\g t v. g=g2 /\ t=tn2 /\ v=s2`, `c2`] >> simp[] >>
  irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qexistsl_tac [`\g t v. g=g3 /\ t=tn3 /\ v=s3`, `c3`] >> simp[];

fun address_resources dynamic_covers =
  `lookup_var sp s4 = SOME (n2w (w2n a + i*ss)) /\
   lookup_var dp s4 = SOME (n2w (w2n b + i*ds)) /\
   s4.vs_memory = s.vs_memory` by
    simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  `tn4.t_imm = tn.t_imm /\ s4.vs_call_ctx = s.vs_call_ctx /\
   s4.vs_accounts = s.vs_accounts /\ s4.vs_transient = s.vs_transient` by
    simp[Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
         step_taint_def, imm_taint_def, mk_inst_def,
         Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         update_var_def] >>
  simp[] >>
  `ptr_covers g3 tn3 sp t3 ss` by
    (simp[Abbr `g3`, Abbr `tn3`, Abbr `t3`] >> irule dynamic_covers >>
     simp[Abbr `s2`, Abbr `s1`, Abbr `g2`, Abbr `g1`,
          Abbr `tn2`, Abbr `tn1`, eval_operand_def,
          ptr_covers_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     conj_tac >- gvs[lookup_var_def] >>
     qexists_tac `S'` >> gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  `ptr_covers g3 tn3 sp s3 ss` by
    gvs[Abbr `s3`, ptr_covers_def, lookup_var_def] >>
  conj_tac >-
    (gvs[Abbr `s4`, Abbr `g4`, Abbr `tn4`, Abbr `t4`,
          ptr_covers_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, copy_len_binop_ghost_frame]) >>
  `ptr_covers g3 tn3 dr s3 T'` by
    (gvs[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `t3`,
         ptr_covers_def, lookup_var_def, update_var_def,
         copy_len_binop_ghost_frame, Abbr `g2`, Abbr `g1`,
         Abbr `tn2`, Abbr `tn1`, Abbr `s2`, Abbr `s1`,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]) >>
  `ptr_covers g4 tn4 dp t4 ds` by
    (simp[Abbr `g4`, Abbr `tn4`, Abbr `t4`] >> irule dynamic_covers >> simp[] >>
     conj_tac >- simp[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
             eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- gvs[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
             lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qexists_tac `T'` >> simp[]) >>
  `ptr_covers g4 tn4 dp s4 ds` by
    gvs[Abbr `s4`, ptr_covers_def, lookup_var_def] >> simp[] >>
  simp[Abbr `g4`, Abbr `tn4`, Abbr `t4`, copy_len_binop_ghost_frame] >>
  simp[Abbr `g3`, Abbr `tn3`, Abbr `t3`, copy_len_binop_ghost_frame] >>
  simp[Abbr `tn2`, Abbr `tn1`] >> rpt strip_tac >>
  simp[copy_len_binop_ghost_frame,
       Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def, FLOOKUP_UPDATE,
       Abbr `g2`, Abbr `g1`, FLOOKUP_DRESTRICT, op_taint_def] >>
  simp[Abbr `s4`, lookup_var_def, update_var_def, FLOOKUP_UPDATE];
end
