#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#include <lean/lean.h>

using namespace cvc5;

extern "C" lean_obj_res except_ok(
  lean_obj_arg alpha,
  lean_obj_arg val
);

extern "C" lean_obj_res except_ok_bool(
  uint8_t val
);

extern "C" lean_obj_res except_ok_u32(
  uint32_t val
);

extern "C" lean_obj_res except_ok_u8(
  uint8_t val
);

extern "C" lean_obj_res except_err(
  lean_obj_arg alpha,
  lean_obj_arg msg
);

#define CVC5_TRY_CATCH_EXCEPT(code) \
  try { \
    code \
  } catch (CVC5ApiException& e) { \
    return except_err(lean_box(0), lean_mk_string(e.what())); \
  } catch (char const* e) { \
    return except_err(lean_box(0), lean_mk_string(e)); \
  } catch (...) { \
    return except_err( \
      lean_box(0), \
      lean_mk_string("cvc5's term manager raised an unexpected exception") \
    ); \
  }

inline lean_obj_res mk_unit_unit() { return lean_box(0); }

inline uint8_t mk_bool_false() { return 0; }

inline uint8_t mk_bool_true() { return 1; }

inline uint8_t bool_box(bool b) { return b ? mk_bool_true() : mk_bool_false(); }

extern "C" lean_obj_res rat_mk(lean_obj_arg num, lean_obj_arg den);

inline bool bool_unbox(uint8_t b) { return static_cast<bool>(b); }

extern "C" lean_obj_res kind_toString(uint16_t k)
{
  return lean_mk_string(std::to_string(static_cast<Kind>(k - 2)).c_str());
}

extern "C" lean_obj_res sortKind_toString(uint8_t sk)
{
  return lean_mk_string(std::to_string(static_cast<SortKind>(sk - 2)).c_str());
}

extern "C" lean_obj_res proofRule_toString(uint8_t pr)
{
  return lean_mk_string(std::to_string(static_cast<ProofRule>(pr)).c_str());
}

extern "C" lean_obj_res proofRewriteRule_toString(uint16_t prr)
{
  return lean_mk_string(
      std::to_string(static_cast<ProofRewriteRule>(prr)).c_str());
}

extern "C" lean_obj_res skolemId_toString(uint8_t si)
{
  return lean_mk_string(std::to_string(static_cast<SkolemId>(si)).c_str());
}

static void result_finalize(void* obj) { delete static_cast<Result*>(obj); }

static void result_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Result` does not contain nested Lean objects
}

static lean_external_class* g_result_class = nullptr;

static inline lean_obj_res result_box(Result* r)
{
  if (g_result_class == nullptr)
  {
    g_result_class =
        lean_register_external_class(result_finalize, result_foreach);
  }
  return lean_alloc_external(g_result_class, r);
}

static inline const Result* result_unbox(b_lean_obj_arg r)
{
  return static_cast<Result*>(lean_get_external_data(r));
}

extern "C" uint8_t result_isSat(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isSat());
}

extern "C" uint8_t result_isUnsat(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnsat());
}

extern "C" uint8_t result_isUnknown(lean_obj_arg r)
{
  return bool_box(result_unbox(r)->isUnknown());
}

extern "C" lean_obj_res result_toString(lean_obj_arg r)
{
  return lean_mk_string(result_unbox(r)->toString().c_str());
}

static void sort_finalize(void* obj) { delete static_cast<Sort*>(obj); }

static void sort_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Sort` does not contain nested Lean objects
}

static lean_external_class* g_sort_class = nullptr;

static inline lean_obj_res sort_box(Sort* s)
{
  if (g_sort_class == nullptr)
  {
    g_sort_class = lean_register_external_class(sort_finalize, sort_foreach);
  }
  return lean_alloc_external(g_sort_class, s);
}

static inline const Sort* sort_unbox(b_lean_obj_arg s)
{
  return static_cast<Sort*>(lean_get_external_data(s));
}

extern "C" lean_obj_res sort_null(lean_obj_arg unit)
{
  return sort_box(new Sort());
}

extern "C" uint8_t sort_getKind(lean_obj_arg s)
{
  return static_cast<int32_t>(sort_unbox(s)->getKind()) + 2;
}

extern "C" uint8_t sort_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*sort_unbox(l) == *sort_unbox(r));
}

extern "C" uint64_t sort_hash(lean_obj_arg s)
{
  return std::hash<Sort>()(*sort_unbox(s));
}

extern "C" uint8_t sort_isFunction(lean_obj_arg s)
{
  return bool_box(sort_unbox(s)->isFunction());
}

extern "C" lean_obj_res sort_getFunctionDomainSorts(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Sort> domains = sort_unbox(s)->getFunctionDomainSorts();
    lean_object* ds = lean_mk_empty_array();
    for (const Sort& domain : domains)
    {
      ds = lean_array_push(ds, sort_box(new Sort(domain)));
    }
    return except_ok(lean_box(0), ds);
  )
}

extern "C" lean_obj_res sort_getFunctionCodomainSort(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(sort_unbox(s)->getFunctionCodomainSort()))
    );
  )
}

extern "C" lean_obj_res sort_getSymbol(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      lean_mk_string(sort_unbox(s)->getSymbol().c_str())
    );
  )
}

extern "C" uint8_t sort_isInteger(lean_obj_arg s)
{
  return bool_box(sort_unbox(s)->isInteger());
}

extern "C" lean_obj_res sort_getBitVectorSize(lean_obj_arg s)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok_u32(
      static_cast<int32_t>(sort_unbox(s)->getBitVectorSize())
    );
  )
}

extern "C" lean_obj_res sort_toString(lean_obj_arg s)
{
  return lean_mk_string(sort_unbox(s)->toString().c_str());
}

static void op_finalize(void* obj) { delete static_cast<Op*>(obj); }

static void op_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Op` does not contain nested Lean objects
}

static lean_external_class* g_op_class = nullptr;

static inline lean_obj_res op_box(Op* op)
{
  if (g_op_class == nullptr)
  {
    g_op_class = lean_register_external_class(op_finalize, op_foreach);
  }
  return lean_alloc_external(g_op_class, op);
}

static inline const Op* op_unbox(b_lean_obj_arg op)
{
  return static_cast<Op*>(lean_get_external_data(op));
}

static inline Op* mut_op_unbox(b_lean_obj_arg op)
{
  return static_cast<Op*>(lean_get_external_data(op));
}

extern "C" lean_obj_res op_null(lean_obj_arg unit) { return op_box(new Op()); }

extern "C" uint16_t op_getKind(lean_obj_arg op)
{
  return static_cast<int32_t>(op_unbox(op)->getKind()) + 2;
}

extern "C" uint8_t op_isNull(lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isNull());
}

extern "C" uint8_t op_isIndexed(lean_obj_arg op)
{
  return bool_box(op_unbox(op)->isIndexed());
}

extern "C" lean_obj_res op_getNumIndices(lean_obj_arg op)
{
  return lean_usize_to_nat(op_unbox(op)->getNumIndices());
}

extern "C" uint8_t op_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*op_unbox(l) == *op_unbox(r));
}

static inline lean_obj_res term_box(Term* t);

extern "C" lean_obj_res op_get(lean_obj_arg op, lean_obj_arg i)
{
  return term_box(new Term((*mut_op_unbox(op))[lean_usize_of_nat(i)]));
}

extern "C" lean_obj_res op_toString(lean_obj_arg op)
{
  return lean_mk_string(op_unbox(op)->toString().c_str());
}

static void term_finalize(void* obj) { delete static_cast<Grammar*>(obj); }

static void term_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Term` does not contain nested Lean objects
}

static lean_external_class* g_term_class = nullptr;

static inline lean_obj_res term_box(Term* t)
{
  if (g_term_class == nullptr)
  {
    g_term_class = lean_register_external_class(term_finalize, term_foreach);
  }
  return lean_alloc_external(g_term_class, t);
}

static inline const Term* term_unbox(b_lean_obj_arg t)
{
  return static_cast<Term*>(lean_get_external_data(t));
}

extern "C" lean_obj_res term_null(lean_obj_arg unit)
{
  return term_box(new Term());
}

extern "C" uint8_t term_isNull(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isNull());
}

extern "C" lean_obj_res term_not(lean_obj_arg t)
{
  return term_box(new Term(term_unbox(t)->notTerm()));
}

extern "C" lean_obj_res term_and(lean_obj_arg t1, lean_obj_arg t2)
{
  return term_box(new Term(term_unbox(t1)->andTerm(*term_unbox(t2))));
}

extern "C" lean_obj_res term_or(lean_obj_arg t1, lean_obj_arg t2)
{
  return term_box(new Term(term_unbox(t1)->orTerm(*term_unbox(t2))));
}

extern "C" lean_obj_res term_toString(lean_obj_arg t)
{
  return lean_mk_string(term_unbox(t)->toString().c_str());
}

extern "C" uint16_t term_getKind(lean_obj_arg t)
{
  return static_cast<int32_t>(term_unbox(t)->getKind()) + 2;
}

extern "C" uint8_t term_hasOp(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasOp());
}

extern "C" lean_obj_res term_getOp(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      op_box(new Op(term_unbox(t)->getOp()))
    );
  )
}

extern "C" lean_obj_arg term_getSort(lean_obj_arg t)
{
  return sort_box(new Sort(term_unbox(t)->getSort()));
}

extern "C" lean_obj_res term_substitute(
  lean_obj_arg term,
  lean_obj_arg terms,
  lean_obj_arg replacements
) {
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Term> ts;
    std::vector<Term> rs;
    for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
    {
      ts.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))
      ));
      rs.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), replacements, lean_usize_to_nat(i))
      ));
    }
    return except_ok(lean_box(0),
      term_box(new Term(term_unbox(term)->substitute(ts, rs)))
    );
  )
}

extern "C" uint8_t term_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*term_unbox(l) == *term_unbox(r));
}

extern "C" uint64_t term_hash(lean_obj_arg t)
{
  return std::hash<Term>()(*term_unbox(t));
}

extern "C" lean_obj_res term_getBooleanValue(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok_bool(
      bool_box(term_unbox(t)->getBooleanValue())
    );
  )
}

extern "C" lean_obj_res term_getBitVectorValue(lean_obj_arg t, uint32_t base)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      lean_mk_string(term_unbox(t)->getBitVectorValue(base).c_str())
    );
  )
}

extern "C" lean_obj_res term_getIntegerValue(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      lean_cstr_to_int(term_unbox(t)->getIntegerValue().c_str())
    );
  )
}

extern "C" lean_obj_res l_Lean_mkRat(lean_obj_arg num, lean_obj_arg den);

extern "C" lean_obj_res term_getRationalValue(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::string r = term_unbox(t)->getRealValue();
    size_t i = r.find('/');
    return except_ok(lean_box(0),
      l_Lean_mkRat(
        lean_cstr_to_int(r.substr(0, i).c_str()), lean_cstr_to_nat(r.substr(i + 1).c_str())
      )
    );
  )
}

extern "C" uint8_t term_hasSymbol(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->hasSymbol());
}

extern "C" lean_obj_res term_getSymbol(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      lean_mk_string(term_unbox(t)->getSymbol().c_str())
    );
  )
}

extern "C" lean_obj_res term_getId(lean_obj_arg t)
{
  return lean_uint64_to_nat(term_unbox(t)->getId());
}

extern "C" lean_obj_res term_getNumChildren(lean_obj_arg t)
{
  return lean_usize_to_nat(term_unbox(t)->getNumChildren());
}

extern "C" uint8_t term_isSkolem(lean_obj_arg t)
{
  return bool_box(term_unbox(t)->isSkolem());
}

extern "C" lean_obj_res term_getSkolemId(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok_u8(
      static_cast<int32_t>(term_unbox(t)->getSkolemId())
    );
  )
}

extern "C" lean_obj_res term_getSkolemIndices(lean_obj_arg t)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Term> args = term_unbox(t)->getSkolemIndices();
    lean_object* as = lean_mk_empty_array();
    for (const Term& arg : args)
    {
      as = lean_array_push(as, term_box(new Term(arg)));
    }
    return except_ok(lean_box(0), as);
  )
}

extern "C" lean_obj_res term_get(lean_obj_arg t, lean_obj_arg i)
{
  return term_box(new Term((*term_unbox(t))[lean_usize_of_nat(i)]));
}

static void proof_finalize(void* obj) { delete static_cast<Proof*>(obj); }

static void proof_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Proof` does not contain nested Lean objects
}

static lean_external_class* g_proof_class = nullptr;

static inline lean_obj_res proof_box(Proof* p)
{
  if (g_proof_class == nullptr)
  {
    g_proof_class = lean_register_external_class(proof_finalize, proof_foreach);
  }
  return lean_alloc_external(g_proof_class, p);
}

static inline const Proof* proof_unbox(b_lean_obj_arg p)
{
  return static_cast<Proof*>(lean_get_external_data(p));
}

extern "C" lean_obj_res proof_null(lean_obj_arg unit)
{
  return proof_box(new Proof());
}

extern "C" uint8_t proof_getRule(lean_obj_arg p)
{
  return static_cast<uint32_t>(proof_unbox(p)->getRule());
}

extern "C" uint16_t proof_getRewriteRule(lean_obj_arg p)
{
  return static_cast<uint32_t>(proof_unbox(p)->getRewriteRule());
}

extern "C" lean_obj_res proof_getResult(lean_obj_arg p)
{
  return term_box(new Term(proof_unbox(p)->getResult()));
}

extern "C" lean_obj_res proof_getChildren(lean_obj_arg p)
{
  std::vector<Proof> children = proof_unbox(p)->getChildren();
  lean_object* cs = lean_mk_empty_array();
  for (const Proof& child : children)
  {
    cs = lean_array_push(cs, proof_box(new Proof(child)));
  }
  return cs;
}

extern "C" lean_obj_res proof_getArguments(lean_obj_arg p)
{
  std::vector<Term> args = proof_unbox(p)->getArguments();
  lean_object* as = lean_mk_empty_array();
  for (const Term& arg : args)
  {
    as = lean_array_push(as, term_box(new Term(arg)));
  }
  return as;
}

extern "C" uint8_t proof_beq(lean_obj_arg l, lean_obj_arg r)
{
  return bool_box(*proof_unbox(l) == *proof_unbox(r));
}

extern "C" uint64_t proof_hash(lean_obj_arg p)
{
  return std::hash<Proof>()(*proof_unbox(p));
}

static void termManager_finalize(void* obj)
{
  delete static_cast<TermManager*>(obj);
}

static void termManager_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `TermManager` does not contain nested Lean objects
}

static lean_external_class* g_termManager_class = nullptr;

static inline lean_obj_res tm_box(TermManager* tm)
{
  if (g_termManager_class == nullptr)
  {
    g_termManager_class =
        lean_register_external_class(termManager_finalize, termManager_foreach);
  }
  return lean_alloc_external(g_termManager_class, tm);
}

static inline const TermManager* tm_unbox(b_lean_obj_arg tm)
{
  return static_cast<TermManager*>(lean_get_external_data(tm));
}

static inline TermManager* mut_tm_unbox(b_lean_obj_arg tm)
{
  return static_cast<TermManager*>(lean_get_external_data(tm));
}

extern "C" lean_obj_res termManager_new(lean_obj_arg unit)
{
  return lean_io_result_mk_ok(tm_box(new TermManager()));
}

extern "C" lean_obj_arg termManager_getBooleanSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getBooleanSort()));
}

extern "C" lean_obj_arg termManager_getIntegerSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getIntegerSort()));
}

extern "C" lean_obj_arg termManager_getRealSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getRealSort()));
}

extern "C" lean_obj_arg termManager_getRegExpSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getRegExpSort()));
}

extern "C" lean_obj_arg termManager_getRoundingModeSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getRoundingModeSort()));
}

extern "C" lean_obj_arg termManager_getStringSort(lean_obj_arg tm)
{
  return sort_box(new Sort(mut_tm_unbox(tm)->getStringSort()));
}

extern "C" lean_obj_res termManager_mkArraySort(lean_obj_arg tm, lean_obj_arg idx, lean_obj_arg elm)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkArraySort(*sort_unbox(idx), *sort_unbox(elm))))
    );
  )
}

extern "C" lean_obj_res termManager_mkBitVectorSort(lean_obj_arg tm, uint32_t size)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkBitVectorSort(size)))
    );
  )
}

extern "C" lean_obj_res termManager_mkFloatingPointSort(
  lean_obj_arg tm,
  uint32_t exp,
  uint32_t sig
)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkFloatingPointSort(exp, sig)))
    );
  )
}

extern "C" lean_obj_res termManager_mkFiniteFieldSort(
  lean_obj_arg tm,
  lean_obj_arg size,
  uint32_t base
)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkFiniteFieldSort(lean_string_cstr(size), base)))
    );
  )
}

extern "C" lean_obj_res termManager_mkFunctionSort(
  lean_obj_arg tm,
  lean_obj_arg sorts,
  lean_obj_arg codomain
)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Sort> cvc5Sorts;
    for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
    {
      cvc5Sorts.push_back(*sort_unbox(
          lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkFunctionSort(cvc5Sorts, *sort_unbox(codomain))))
    );
  )
}

extern "C" lean_obj_res termManager_mkPredicateSort(
  lean_obj_arg tm,
  lean_obj_arg sorts
)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Sort> cvc5Sorts;
    for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i)
    {
      cvc5Sorts.push_back(*sort_unbox(
          lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkPredicateSort(cvc5Sorts)))
    );
  )
}

extern "C" lean_obj_res termManager_mkUninterpretedSort(
  lean_obj_arg tm,
  lean_obj_arg symbol
)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkUninterpretedSort(lean_string_cstr(symbol))))
    );
  )
}

extern "C" lean_obj_res termManager_mkParamSort(
  lean_obj_arg tm,
  lean_obj_arg symbol
)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      sort_box(new Sort(mut_tm_unbox(tm)->mkParamSort(lean_string_cstr(symbol))))
    );
  )
}

extern "C" lean_obj_res termManager_mkBoolean(lean_obj_arg tm, uint8_t val)
{
  return term_box(new Term(mut_tm_unbox(tm)->mkBoolean(bool_unbox(val))));
}

extern "C" lean_obj_res termManager_mkIntegerFromString(lean_obj_arg tm,
                                                        lean_obj_arg val)
{
  CVC5_TRY_CATCH_EXCEPT(
    return except_ok(lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkInteger(lean_string_cstr(val))))
    );
  )
}

extern "C" lean_obj_res termManager_mkTerm(lean_obj_arg tm,
                                           uint16_t kind,
                                           lean_obj_arg children)
{
  CVC5_TRY_CATCH_EXCEPT(
    Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
    std::vector<Term> cs;
    for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
    {
      cs.push_back(*term_unbox(
          lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(k, cs)))
    );
  )
}

extern "C" lean_obj_res termManager_mkTermOfOp(
  lean_obj_arg tm,
  lean_obj_arg op,
  lean_obj_arg children
)
{
  CVC5_TRY_CATCH_EXCEPT(
    std::vector<Term> cs;
    for (size_t i = 0, n = lean_array_size(children); i < n; ++i)
    {
      cs.push_back(*term_unbox(
          lean_array_get(term_box(new Term()), children, lean_usize_to_nat(i))));
    }
    return except_ok(lean_box(0),
      term_box(new Term(mut_tm_unbox(tm)->mkTerm(*op_unbox(op), cs)))
    );
  )
}

extern "C" lean_obj_res termManager_mkConst(
  lean_obj_arg tm,
  lean_obj_arg sort,
  lean_obj_arg symbol
)
{
  return term_box(new Term(mut_tm_unbox(tm)->mkConst(*sort_unbox(sort), lean_string_cstr(symbol))));
}

extern "C" lean_obj_res termManager_mkVar(
  lean_obj_arg tm,
  lean_obj_arg sort,
  lean_obj_arg symbol
)
{
  return term_box(new Term(mut_tm_unbox(tm)->mkVar(*sort_unbox(sort), lean_string_cstr(symbol))));
}

extern "C" lean_obj_res termManager_mkOpOfIndices(
  lean_obj_arg tm,
  uint16_t kind,
  lean_obj_arg args
)
{
  CVC5_TRY_CATCH_EXCEPT(
    Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
    std::vector<uint32_t> indices;
    for (size_t i = 0, n = lean_array_size(args); i < n; ++i)
    {
      indices.push_back(
        lean_uint32_of_nat(lean_array_get(0, args, lean_usize_to_nat(i)))
      );
    }
    return except_ok(lean_box(0),
      op_box(new Op(mut_tm_unbox(tm)->mkOp(k, indices)))
    );
  )
}

extern "C" lean_obj_res termManager_mkOpOfString(
  lean_obj_arg tm,
  uint16_t kind,
  lean_obj_arg arg
)
{
  Kind k = static_cast<Kind>(static_cast<int32_t>(kind) - 2);
  return op_box(new Op(mut_tm_unbox(tm)->mkOp(k, lean_string_cstr(arg))));
}

static void solver_finalize(void* obj) { delete static_cast<Solver*>(obj); }

static void solver_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Solver` does not contain nested Lean objects
}

static lean_external_class* g_solver_class = nullptr;

static inline lean_obj_res solver_box(Solver* s)
{
  if (g_solver_class == nullptr)
  {
    g_solver_class =
        lean_register_external_class(solver_finalize, solver_foreach);
  }
  return lean_alloc_external(g_solver_class, s);
}

static inline Solver* solver_unbox(b_lean_obj_arg s)
{
  return static_cast<Solver*>(lean_get_external_data(s));
}

extern "C" lean_obj_res solver_val(lean_obj_arg m,
                                   lean_obj_arg inst,
                                   lean_obj_arg alpha,
                                   lean_obj_arg a,
                                   lean_obj_arg solver);

extern "C" lean_obj_res solver_err(lean_obj_arg m,
                                   lean_obj_arg inst,
                                   lean_obj_arg alpha,
                                   lean_obj_arg e,
                                   lean_obj_arg solver);

extern "C" lean_obj_res solver_errOfString(
  lean_obj_arg m,
  lean_obj_arg inst,
  lean_obj_arg alpha,
  lean_obj_arg msg,
  lean_obj_arg solver
);

#define CVC5_TRY_CATCH_SOLVER(fnName, inst, solver, code) \
  try { \
    code \
  } catch (CVC5ApiException& e) { \
    return solver_errOfString( \
      lean_box(0), inst, lean_box(0), lean_mk_string(e.what()), solver \
    ); \
  } catch (char const* e) { \
    return solver_errOfString( \
      lean_box(0), inst, lean_box(0), lean_mk_string(e), solver \
    ); \
  } catch (...) { \
    return solver_errOfString( \
      lean_box(0), inst, lean_box(0), \
      lean_mk_string("cvc5 raised an unexpected exception"), solver \
    ); \
  }

extern "C" lean_obj_res solver_new(lean_obj_arg tm)
{
  return solver_box(new Solver(*mut_tm_unbox(tm)));
}

extern "C" lean_obj_res solver_getVersion(lean_obj_arg inst,
                                          lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_getVersion", inst, solver,
    return solver_val(lean_box(0),
                      inst,
                      lean_box(0),
                      lean_mk_string(solver_unbox(solver)->getVersion().c_str()),
                      solver);
  )
}

extern "C" lean_obj_res solver_setOption(lean_obj_arg inst,
                                         lean_object* option,
                                         lean_object* value,
                                         lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_setOption", inst, solver,
    solver_unbox(solver)->setOption(lean_string_cstr(option),
                                    lean_string_cstr(value));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_resetAssertions(
  lean_obj_arg inst,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_resetAssertions", inst, solver,
    solver_unbox(solver)->resetAssertions();
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_setLogic(
  lean_obj_arg inst,
  lean_object* logic,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_setLogic", inst, solver,
    solver_unbox(solver)->setLogic(lean_string_cstr(logic));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_simplify(
  lean_obj_arg inst,
  lean_obj_arg term,
  lean_obj_arg applySubs,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_simplify", inst, solver,
    Term value = solver_unbox(solver)->simplify(
      *term_unbox(term),
      bool_unbox(lean_unbox(applySubs))
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_getInterpolant(
  lean_obj_arg inst,
  lean_obj_arg term,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_getInterpolant", inst, solver,
    Term value = solver_unbox(solver)->getInterpolant(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_getInterpolantNext(
  lean_obj_arg inst,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_getInterpolantNext", inst, solver,
    Term value = solver_unbox(solver)->getInterpolantNext();
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_getAbduct(
  lean_obj_arg inst,
  lean_obj_arg term,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_getAbduct", inst, solver,
    Term value = solver_unbox(solver)->getAbduct(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_getAbductNext(
  lean_obj_arg inst,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_getAbductNext", inst, solver,
    Term value = solver_unbox(solver)->getAbductNext();
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_getQuantifierElimination(
  lean_obj_arg inst,
  lean_obj_arg term,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_getQuantifierElimination", inst, solver,
    Term value = solver_unbox(solver)->getQuantifierElimination(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_getQuantifierEliminationDisjunct(
  lean_obj_arg inst,
  lean_obj_arg term,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_getQuantifierEliminationDisjunct", inst, solver,
    Term value = solver_unbox(solver)->getQuantifierEliminationDisjunct(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(value)), solver);
  )
}

extern "C" lean_obj_res solver_declareFun(
  lean_obj_arg inst,
  lean_obj_arg symbol,
  lean_obj_arg sorts,
  lean_obj_arg sort,
  lean_obj_arg fresh,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_declareFun", inst, solver,
    std::vector<Sort> sort_vec;
    for (size_t i = 0, n = lean_array_size(sorts); i < n; ++i) {
      sort_vec.push_back(*sort_unbox(
        lean_array_get(sort_box(new Sort()), sorts, lean_usize_to_nat(i))
      ));
    }
    Term f = solver_unbox(solver)->declareFun(
      lean_string_cstr(symbol),
      sort_vec,
      *sort_unbox(sort),
      bool_unbox(lean_unbox(fresh))
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  )
}

extern "C" lean_obj_res solver_declareSort(
  lean_obj_arg inst,
  lean_obj_arg symbol,
  lean_obj_arg arity,
  lean_obj_arg fresh,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_declareSort", inst, solver,
    Sort s = solver_unbox(solver)->declareSort(
      lean_string_cstr(symbol),
      lean_uint32_of_nat(arity),
      bool_unbox(lean_unbox(fresh))
    );
    return solver_val(lean_box(0), inst, lean_box(0), sort_box(new Sort(s)), solver);
  )
}

extern "C" lean_obj_res solver_assertFormula(lean_obj_arg inst,
                                             lean_object* term,
                                             lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_assertFormula", inst, solver,
    solver_unbox(solver)->assertFormula(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_checkSat(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_checkSat", inst, solver,
    return solver_val(lean_box(0),
                      inst,
                      lean_box(0),
                      result_box(new Result(solver_unbox(solver)->checkSat())),
                      solver);
  )
}

extern "C" lean_obj_res solver_checkSatAssuming(
  lean_obj_arg inst,
  lean_obj_arg assumptions,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_checkSatAssuming", inst, solver,
    std::vector<Term> formulas;
    for (size_t i = 0, n = lean_array_size(assumptions); i < n; ++i)
    {
      formulas.push_back(
        *term_unbox(
          lean_array_get(term_box(new Term()), assumptions, lean_usize_to_nat(i))
        )
      );
    }
    Result res = solver_unbox(solver)->checkSatAssuming(formulas);
    return solver_val(lean_box(0), inst, lean_box(0), result_box(new Result(res)), solver);
  )
}

extern "C" lean_obj_res solver_getModelDomainElements(
  lean_obj_arg inst,
  lean_obj_arg sort,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_getModelDomainElements", inst, solver,
    std::vector<Term> vals = solver_unbox(solver)->getModelDomainElements(*sort_unbox(sort));
    lean_object* values = lean_mk_empty_array();
    for (const Term& value : vals) {
      values = lean_array_push(values, term_box(new Term(value)));
    }
    return solver_val(lean_box(0), inst, lean_box(0), values, solver);
  )
}

extern "C" lean_obj_res solver_getValue(
  lean_obj_arg inst,
  lean_object * term,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_getValue", inst, solver,
    Term val = solver_unbox(solver)->getValue(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(val)), solver);
  )
}

extern "C" lean_obj_res solver_getValues(
  lean_obj_arg inst,
  lean_obj_arg terms,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_getValues", inst, solver,
    std::vector<Term> ts;
    for (size_t i = 0, n = lean_array_size(terms); i < n; ++i)
    {
      ts.push_back(
        *term_unbox(
          lean_array_get(term_box(new Term()), terms, lean_usize_to_nat(i))
        )
      );
    }
    std::vector<Term> vals = solver_unbox(solver)->getValue(ts);
    lean_object* values = lean_mk_empty_array();
    for (const Term& value : vals) {
      values = lean_array_push(values, term_box(new Term(value)));
    }
    return solver_val(lean_box(0), inst, lean_box(0), values, solver);
  )
}

extern "C" lean_obj_res solver_getProof(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_getProof", inst, solver,
    std::vector<Proof> proofs = solver_unbox(solver)->getProof();
    lean_object* ps = lean_mk_empty_array();
    for (const Proof& proof : proofs)
    {
      ps = lean_array_push(ps, proof_box(new Proof(proof)));
    }
    return solver_val(lean_box(0), inst, lean_box(0), ps, solver);
  )
}

extern "C" lean_obj_res solver_proofToString(lean_obj_arg inst,
                                             lean_obj_arg proof,
                                             lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_proofToString", inst, solver,
    return solver_val(
        lean_box(0),
        inst,
        lean_box(0),
        lean_mk_string(
            solver_unbox(solver)->proofToString(*proof_unbox(proof)).c_str()),
        solver);
  )
}

extern "C" lean_obj_res solver_parse(lean_obj_arg inst,
                                     lean_obj_arg query,
                                     lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_parse", inst, solver,
    Solver* slv = solver_unbox(solver);
    // construct an input parser associated the solver above
    parser::InputParser parser(slv);
    // get the symbol manager of the parser, used when invoking commands below
    parser::SymbolManager* sm = parser.getSymbolManager();
    parser.setStringInput(
        modes::InputLanguage::SMT_LIB_2_6, lean_string_cstr(query), "lean-smt");
    // parse commands until finished
    std::stringstream out;
    parser::Command cmd;
    while (true)
    {
      cmd = parser.nextCommand();
      if (cmd.isNull())
      {
        break;
      }
      // invoke the command on the solver and the symbol manager, print the result
      // to out
      cmd.invoke(slv, sm, out);
    }
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_declareSygusVar(
  lean_obj_arg inst,
  lean_obj_arg symbol,
  lean_obj_arg sort,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_declareSygusVar", inst, solver,
    Term v = solver_unbox(solver)->declareSygusVar(
      lean_string_cstr(symbol),
      *sort_unbox(sort)
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(v)), solver);
  )
}

static void grammar_finalize(void* obj) { delete static_cast<Grammar*>(obj); }

static void grammar_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `Grammar` does not contain nested Lean objects
}

static lean_external_class* g_grammar_class = nullptr;

static inline lean_obj_res grammar_box(Grammar* g)
{
  if (g_grammar_class == nullptr)
  {
    g_grammar_class = lean_register_external_class(grammar_finalize, grammar_foreach);
  }
  return lean_alloc_external(g_grammar_class, g);
}

static inline const Grammar* grammar_unbox(b_lean_obj_arg g)
{
  return static_cast<Grammar*>(lean_get_external_data(g));
}

extern "C" lean_obj_res grammar_null(lean_obj_arg unit)
{
  return grammar_box(new Grammar());
}

extern "C" uint8_t grammar_isNull(lean_obj_arg g)
{
  return bool_box(grammar_unbox(g)->isNull());
}

extern "C" lean_obj_res grammar_addRule(
  lean_obj_arg g,
  lean_object* ntSymbol,
  lean_object* rule
) {
  Grammar gram = *grammar_unbox(g);
  gram.addRule(*term_unbox(ntSymbol), *term_unbox(rule));
  return grammar_box(new Grammar(gram));
}

extern "C" lean_obj_res grammar_toString(lean_obj_arg g)
{
  return lean_mk_string(grammar_unbox(g)->toString().c_str());
}

extern "C" lean_obj_res solver_mkGrammar(
  lean_obj_arg inst,
  lean_obj_arg boundVars,
  lean_obj_arg ntSymbols,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_mkGrammar", inst, solver,
    std::vector<Term> boundVars_vec;
    for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i) {
      boundVars_vec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))
      ));
    }
    std::vector<Term> ntSymbols_vec;
    for (size_t i = 0, n = lean_array_size(ntSymbols); i < n; ++i) {
      ntSymbols_vec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), ntSymbols, lean_usize_to_nat(i))
      ));
    }
    Grammar g = solver_unbox(solver)->mkGrammar(
      boundVars_vec,
      ntSymbols_vec
    );
    return solver_val(lean_box(0), inst, lean_box(0), grammar_box(new Grammar(g)), solver);
  )
}

extern "C" lean_obj_res solver_synthFun(
  lean_obj_arg inst,
  lean_obj_arg symbol,
  lean_obj_arg boundVars,
  lean_obj_arg sort,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_synthFun", inst, solver,
    std::vector<Term> boundVars_vec;
    for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i) {
      boundVars_vec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))
      ));
    }
    Term f = solver_unbox(solver)->synthFun(
      lean_string_cstr(symbol),
      boundVars_vec,
      *sort_unbox(sort)
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  )
}

extern "C" lean_obj_res solver_synthFunWith(
  lean_obj_arg inst,
  lean_obj_arg symbol,
  lean_obj_arg boundVars,
  lean_obj_arg sort,
  lean_object* grammar,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_synthFunWith", inst, solver,
    std::vector<Term> boundVars_vec;
    for (size_t i = 0, n = lean_array_size(boundVars); i < n; ++i) {
      boundVars_vec.push_back(*term_unbox(
        lean_array_get(term_box(new Term()), boundVars, lean_usize_to_nat(i))
      ));
    }
    Grammar gram = *grammar_unbox(grammar);
    Term f = solver_unbox(solver)->synthFun(
      lean_string_cstr(symbol),
      boundVars_vec,
      *sort_unbox(sort),
      gram
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  )
}

extern "C" lean_obj_res solver_addSygusConstraint(
  lean_obj_arg inst,
  lean_object* term,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_addSygusConstraint", inst, solver,
    solver_unbox(solver)->addSygusConstraint(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_getSygusConstraints(
  lean_obj_arg inst,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_getSygusConstraints", inst, solver,
    std::vector<Term> cs = solver_unbox(solver)->getSygusConstraints();
    lean_object* constraints = lean_mk_empty_array();
    for (const Term& value : cs) {
      constraints = lean_array_push(constraints, term_box(new Term(value)));
    }
    return solver_val(lean_box(0), inst, lean_box(0), constraints, solver);
  )
}

extern "C" lean_obj_res solver_addSygusAssume(
  lean_obj_arg inst,
  lean_object* term,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_addSygusAssume", inst, solver,
    solver_unbox(solver)->addSygusAssume(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

extern "C" lean_obj_res solver_getSygusAssumptions(
  lean_obj_arg inst,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_getSygusAssumptions", inst, solver,
    std::vector<Term> cs = solver_unbox(solver)->getSygusAssumptions();
    lean_object* constraints = lean_mk_empty_array();
    for (const Term& value : cs) {
      constraints = lean_array_push(constraints, term_box(new Term(value)));
    }
    return solver_val(lean_box(0), inst, lean_box(0), constraints, solver);
  )
}

extern "C" lean_obj_res solver_addSygusInvConstraint(
  lean_obj_arg inst,
  lean_object* inv,
  lean_object* pre,
  lean_object* trans,
  lean_object* post,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_addSygusInvConstraint", inst, solver,
    solver_unbox(solver)->addSygusInvConstraint(
      *term_unbox(inv), *term_unbox(pre), *term_unbox(trans), *term_unbox(post)
    );
    return solver_val(lean_box(0), inst, lean_box(0), mk_unit_unit(), solver);
  )
}

static void synthResult_finalize(void* obj) { delete static_cast<SynthResult*>(obj); }

static void synthResult_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `SynthResult` does not contain nested Lean objects
}

static lean_external_class* g_synthResult_class = nullptr;

static inline lean_obj_res synthResult_box(SynthResult* t)
{
  if (g_synthResult_class == nullptr)
  {
    g_synthResult_class = lean_register_external_class(synthResult_finalize, synthResult_foreach);
  }
  return lean_alloc_external(g_synthResult_class, t);
}

static inline const SynthResult* synthResult_unbox(b_lean_obj_arg t)
{
  return static_cast<SynthResult*>(lean_get_external_data(t));
}

extern "C" lean_obj_res synthResult_null(lean_obj_arg unit)
{
  return synthResult_box(new SynthResult());
}

extern "C" uint8_t synthResult_isNull(lean_obj_arg t)
{
  return bool_box(synthResult_unbox(t)->isNull());
}

extern "C" uint8_t synthResult_hasSolution(lean_obj_arg t)
{
  return bool_box(synthResult_unbox(t)->hasSolution());
}

extern "C" uint8_t synthResult_hasNoSolution(lean_obj_arg t)
{
  return bool_box(synthResult_unbox(t)->hasNoSolution());
}

extern "C" uint8_t synthResult_isUnknown(lean_obj_arg t)
{
  return bool_box(synthResult_unbox(t)->isUnknown());
}

extern "C" lean_obj_res synthResult_toString(lean_obj_arg g)
{
  return lean_mk_string(synthResult_unbox(g)->toString().c_str());
}

extern "C" lean_obj_res solver_checkSynth(lean_obj_arg inst, lean_obj_arg solver)
{
  CVC5_TRY_CATCH_SOLVER("solver_checkSynth", inst, solver,
    return solver_val(
      lean_box(0), inst, lean_box(0),
      synthResult_box(new SynthResult(solver_unbox(solver)->checkSynth())),
      solver
    );
  )
}

extern "C" lean_obj_res solver_getSynthSolution(
  lean_obj_arg inst,
  lean_object * term,
  lean_obj_arg solver
)
{
  CVC5_TRY_CATCH_SOLVER("solver_getSynthSolution", inst, solver,
    Term val = solver_unbox(solver)->getSynthSolution(*term_unbox(term));
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(val)), solver);
  )
}

static void findSynthTarget_finalize(void* obj) {
  delete static_cast<modes::FindSynthTarget*>(obj);
}

static void findSynthTarget_foreach(void*, b_lean_obj_arg)
{
  // do nothing since `FindSynthTarget` does not contain nested Lean objects
}

static lean_external_class* g_findSynthTarget_class = nullptr;

static inline lean_obj_res findSynthTarget_box(modes::FindSynthTarget* t)
{
  if (g_findSynthTarget_class == nullptr)
  {
    g_findSynthTarget_class =
      lean_register_external_class(findSynthTarget_finalize, findSynthTarget_foreach);
  }
  return lean_alloc_external(g_findSynthTarget_class, t);
}

static inline const modes::FindSynthTarget* findSynthTarget_unbox(b_lean_obj_arg t)
{
  return static_cast<modes::FindSynthTarget*>(lean_get_external_data(t));
}

extern "C" lean_obj_res findSynthTarget_null(lean_obj_arg unit)
{
  return findSynthTarget_box(new modes::FindSynthTarget());
}

// extern "C" uint8_t findSynthTarget_isNull(lean_obj_arg t)
// {
//   return bool_box(findSynthTarget_unbox(t)->isNull());
// }

extern "C" lean_obj_res solver_findSynth(
  lean_obj_arg inst,
  lean_object* fst,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_findSynth", inst, solver,
    Term f = solver_unbox(solver)->findSynth(
      *findSynthTarget_unbox(fst)
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  )
}

extern "C" lean_obj_res solver_findSynthWith(
  lean_obj_arg inst,
  lean_object* fst,
  lean_object* grammar,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_findSynthWith", inst, solver,
    Grammar gram = *grammar_unbox(grammar);
    Term f = solver_unbox(solver)->findSynth(
      *findSynthTarget_unbox(fst), gram
    );
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  )
}

extern "C" lean_obj_res solver_findSynthNext(
  lean_obj_arg inst,
  lean_obj_arg solver
) {
  CVC5_TRY_CATCH_SOLVER("solver_findSynthNext", inst, solver,
    Term f = solver_unbox(solver)->findSynthNext();
    return solver_val(lean_box(0), inst, lean_box(0), term_box(new Term(f)), solver);
  )
}
