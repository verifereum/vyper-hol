(* ECRecover compiler splitting for the memory proof. *)
Theory bodyMemBiECRecoverRun
Ancestors
  exprSimPrecompiles exprSimDefs exprSimProps exprLowering exprLoweringProps
  exprSimWordArgs exprSimHypsDefs vyperTyping vyperAST vyperTypeSystem
  compileEnv list rich_list builtinMisc loweringPosts exprBopLowering
  vyperInterpreter vyperState vyperContext vyperValue vyperTypeInvariants
  valueEncoding integer_word words byte exprSimAlloc exprSimLiteralBuffer
  exprSimOps emitHelper emitHelperProps fragExec venomExecSemantics
  venomMemDefs venomState venomInst ASCIInumbers dftCommutation
  abiDecodeStaticProps immutableMemoryFrame valueEncodingProps context
  loweringHalt exprSimHash valueEncodingProofs valueCopy extCallOracle
  venomCallOracleDefs vfmTypes
Libs
  monadsyntax

Theorem compile_ecrecover_split:
  compile_ecrecover h v r sig sf = (res,sb) ==>
  ?ip op sm.
    (do ib <- context$compile_alloc_buffer 128;
        emit_void MSTORE [ib.buf_operand; h];
        p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [p1; v];
        p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [p2; r];
        p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [p3; sig];
        ob <- context$compile_alloc_buffer 32;
        emit_void MSTORE [ob.buf_operand; Lit 0w];
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 1w; ip; Lit 128w; op; Lit 32w];
        emit_void ASSERT [success]; emit_op MLOAD [op] od) sm = (res,sb) /\
    LENGTH sf.cs_current_insts <= LENGTH sm.cs_current_insts
Proof
  rewrite_tac[compile_ecrecover_prefix] >>
  pure_once_rewrite_tac[comp_bind_def] >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> strip_tac >>
  rename1 `_ sf = (ipop,sm)` >> PairCases_on `ipop` >> fs[] >>
  rename1 `_ sf = ((ip,op),sm)` >>
  qpat_x_assum `(\(x,y). _) _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[pairTheory.UNCURRY_DEF] >> strip_tac >>
  qexistsl_tac [`ip`, `op`, `sm`] >>
  conj_tac >- gvs[comp_bind_def] >>
  conj_tac >- gvs[comp_bind_def] >>
  qpat_x_assum `_ sf = ((ip,op),sm)` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

