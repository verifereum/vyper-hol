(* Conditional, fixed-calldata composition of joint registration steps. *)
Theory defaultRegistrationFold
Ancestors moduleLowering compileEnv vyperCalldata fragGasPathMem
  fragGasOriginPtr fragGasOriginPtrLoop list arithmetic

(* R is the concrete caller's induction interface, not an execution oracle.
   It tracks compiler/source coherence and distinct names, cursor and fixed
   calldata, allocation frontier/history and future vacant IDs, plus the
   cumulative backed owners and full entry-field frame. The word/bytes step
   theorems supply allocation maps, operand/ghost freshness, decode frames,
   alloca resources and entry record frames at ONE endpoint. Transport of old
   owners through those frames, compiler coherence, natural/modular offset
   bounds, and R initialization are obligations of the concrete join; they
   are deliberately not claimed as unconditional results of this fold. *)

Theorem default_registration_cons_factor[local]:
  compile_register_positional_args ce ((name,prim,dyn,sz,info)::rest) off st =
    (cef,sa) ==>
  ?ce1 st1.
    compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,st1) /\
    compile_register_positional_args ce1 rest (off+sz) st1 = (cef,sa)
Proof
  simp[Once compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars name` >> simp[]
  >- (strip_tac >> qexistsl [`ce`,`st`] >>
      simp[compile_register_positional_args_def, comp_return_def]) >>
  Cases_on `var_location_memory_size x` >> simp[]
  >- (strip_tac >> qexistsl [`ce`,`st`] >>
      simp[compile_register_positional_args_def, comp_return_def]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qexistsl [`ce with ce_vars updated_by (\m. m |+ (name,PtrVar buf.buf_operand x'))`,`cs''`] >>
  simp[compile_register_positional_args_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def]
QED

Theorem default_registration_joint_fold:
  (!ce st off name prim dyn sz info rest tv tvs s G tn owners ce1 st1 x.
    4 <= off /\ ~s.vs_halted /\
    R ce st off ((name,prim,dyn,sz,info)::rest) (tv::tvs) s G tn owners /\
    compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,st1) /\
    calldata_decode_args cd [tv] (off-4) = SOME [x] ==>
    sz = tv_abi_size tv /\
    ?t H1 u1 owner.
      value_of owner = x /\ ~t.vs_halted /\
      R ce1 st1 (off+sz) rest tvs t H1 u1 (owners++[owner]) /\
      gas_path_mem ctx fn s 0 (OK t) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,H1,u1)) /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H1 u1 t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)) ==>
  !specs tvs off ce st cef sa vals s G tn owners.
    4 <= off /\ ~s.vs_halted /\ LENGTH specs = LENGTH tvs /\
    compile_register_positional_args ce specs off st = (cef,sa) /\
    calldata_decode_args cd tvs (off-4) = SOME vals /\
    R ce st off specs tvs s G tn owners ==>
    ?out H u newowners.
      ~out.vs_halted /\
      R cef sa (off + SUM (MAP (\(_,_,_,sz,_). sz) specs)) [] []
        out H u (owners++newowners) /\
      MAP value_of newowners = vals /\
      gas_path_mem ctx fn s 0 (OK out) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK out,H,u)) /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u out) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_tac >> Induct_on `specs`
  >- (rpt gen_tac >> Cases_on `tvs` >>
      simp[compile_register_positional_args_def, comp_return_def,
           calldata_decode_args_def] >> rpt strip_tac >> gvs[] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[gas_path_mem_rules, gas_origin_ptr_path_rules]) >>
  gen_tac >> Cases_on `tvs` >> simp[] >>
  PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  drule default_registration_cons_factor >> strip_tac >>
  qpat_x_assum `calldata_decode_args cd (h'::t) _ = SOME vals` mp_tac >>
  simp[Once calldata_decode_args_def, AllCaseEqs()] >> strip_tac >>
  `calldata_decode_args cd [h'] (off-4) = SOME [v]` by
    simp[calldata_decode_args_def] >>
  qpat_x_assum `!ce st off name prim dyn sz info rest tv tvs s G tn owners ce1 st1 x. _`
    drule_all >> strip_tac >>
  `4 <= off+h3` by decide_tac >>
  `calldata_decode_args cd t (off+h3-4) = SOME vs` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`out`,`H`,`u`,`owner::newowners`] >>
  `owners ++ [owner] ++ newowners = owners ++ owner::newowners` by
    simp[APPEND_ASSOC] >>
  `off+h3 + SUM (MAP (\(_,_,_,sz,_). sz) specs) =
    h3 + (off + SUM (MAP (\(_,_,_,sz,_). sz) specs))` by decide_tac >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_x_assum `R cef sa _ [] [] out H u _` mp_tac >>
      pure_asm_rewrite_tac [] >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  metis_tac[]
QED
