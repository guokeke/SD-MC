/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2012  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.util.predicates.mathsat5;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.cpachecker.util.predicates.mathsat5.Mathsat5NativeApi.*;

import java.io.File;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sosy_lab.common.LogManager;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.FileOption.Type;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.util.predicates.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaList;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.mathsat5.Mathsat5NativeApi.NamedTermsWrapper;

@Options(prefix = "cpa.predicate.mathsat")
public abstract class Mathsat5FormulaManager implements FormulaManager {

  protected static interface MsatType {
    long getVariableType(long msatEnv);
  }

  @Option(description = "Use UIFs (recommended because its more precise)")
  private boolean useUIFs = true;

  @Option(description = "Use theory of EUF in solver (recommended if UIFs are used, otherwise they are useless)")
  private boolean useEUFtheory = true;

  @Option(description = "Export solver queries in Smtlib format into a file (for Mathsat5).")
  private boolean logAllQueries = false;
  @Option(description = "Export solver queries in Smtlib format into a file (for Mathsat5).")
  @FileOption(Type.OUTPUT_FILE)
  private File logfile = new File("mathsat5.%d.smt2");

  private int logfileCounter = 0;

  // the MathSAT environment in which all terms are created
  // default visibility because its heavily used in sub-classes
  final long msatEnv;

  // UF encoding of some unsupported operations
  private final long stringLitUfDecl;

  // datatype to use for variables, when converting them to mathsat vars
  // can be either MSAT_REAL or MSAT_INT
  final long msatVarType;

  // the character for separating name and index of a value
  private static final String INDEX_SEPARATOR = "@";

  // variable name and index that is used for replacing UIFs when they are disabled
  private static final String UIF_VARIABLE = "__uif__";
  private int uifVariableCounter = 0;

  // various caches for speeding up expensive tasks
  //
  // cache for splitting arithmetic equalities in extractAtoms
  private final Map<Formula, Boolean> arithCache = new HashMap<Formula, Boolean>();

  // cache for uninstantiating terms (see uninstantiate() below)
  private final Map<Formula, Formula> uninstantiateCache = new HashMap<Formula, Formula>();

  private final Formula trueFormula;
  private final Formula falseFormula;

  Mathsat5FormulaManager(Configuration config, LogManager logger, MsatType pVarType) throws InvalidConfigurationException {
    config.inject(this, Mathsat5FormulaManager.class);


    long msatConf = msat_create_config();

    msatEnv = msat_create_env(msatConf);
    msatVarType = pVarType.getVariableType(msatEnv);

    trueFormula = encapsulate(msat_make_true(msatEnv));
    falseFormula = encapsulate(msat_make_false(msatEnv));

    long integer_type = msat_get_integer_type(msatEnv);

    long stringLitUfDeclType = msat_get_function_type(msatEnv, new long[] { integer_type }, 1, msatVarType);
    stringLitUfDecl = msat_declare_function(msatEnv, "__string__", stringLitUfDeclType);
  }

  long getMsatEnv() {
    return msatEnv;
  }

  long createEnvironment(long cfg, boolean shared, boolean ghostFilter) {
    long env;

    if (ghostFilter) {
      msat_set_option(cfg, "ghost_filtering", "true");
    }

    if (!useEUFtheory) {
      msat_set_option(cfg, "theory.euf.enabled", "false");
    }

    if (logAllQueries && logfile != null) {
      String filename = String.format(logfile.getAbsolutePath(), logfileCounter++);

      msat_set_option(cfg, "debug.api_call_trace", "1");
      msat_set_option(cfg, "debug.api_call_trace_filename", filename);
    }

    if (shared) {
      env = msat_create_shared_env(cfg, msatEnv);
    } else {
      env = msat_create_env(cfg);
    }

    return env;
  }

  static long getTerm(Formula f) {
    return ((Mathsat5Formula) f).getTerm();
  }

  static long[] getTerm(FormulaList f) {
    return ((Mathsat5FormulaList) f).getTerms();
  }

  protected Formula encapsulate(long t) {
    return new Mathsat5Formula(msatEnv, t);
  }

  private static FormulaList encapsulate(long[] t) {
    return new Mathsat5FormulaList(t);
  }

  private static String makeName(String name, int idx) {
    return name + INDEX_SEPARATOR + idx;
  }

  static Pair<String, Integer> parseName(String var) {
    String[] s = var.split(INDEX_SEPARATOR);
    if (s.length != 2) { throw new IllegalArgumentException("Not an instantiated variable: " + var); }

    return Pair.of(s[0], Integer.parseInt(s[1]));
  }

  abstract long interpreteBitvector(long bv);

  // ----------------- Boolean formulas -----------------

  @Override
  public boolean isBoolean(Formula f) {
    long a = msat_term_get_type(getTerm(f));
    return msat_is_bool_type(msatEnv, a);
  }

  @Override
  public Formula makeTrue() {
    return trueFormula;
  }

  @Override
  public Formula makeFalse() {
    return falseFormula;
  }

  @Override
  public Formula makeNot(Formula f) {
    return encapsulate(msat_make_not(msatEnv, getTerm(f)));
  }

  @Override
  public Formula makeAnd(Formula f1, Formula f2) {
    return encapsulate(msat_make_and(msatEnv, getTerm(f1), getTerm(f2)));
  }

  @Override
  public Formula makeOr(Formula f1, Formula f2) {
    return encapsulate(msat_make_or(msatEnv, getTerm(f1), getTerm(f2)));
  }

  @Override
  public Formula makeEquivalence(Formula f1, Formula f2) {

    long f1Type = msat_term_get_type(getTerm(f1));
    long f2Type = msat_term_get_type(getTerm(f2));

    // there currently exists a bug in the msat-api, where make_equal with 2 bool-types results in error-term
    if (msat_is_bool_type(msatEnv, f1Type) && msat_is_bool_type(msatEnv, f2Type)) {
      return encapsulate(msat_make_iff(msatEnv, getTerm(f1), getTerm(f2)));
    } else {
      return encapsulate(msat_make_equal(msatEnv, getTerm(f1), getTerm(f2)));
    }



  }

  @Override
  public Formula makeIfThenElse(Formula condition, Formula f1, Formula f2) {
    long t;
    long f1Type = msat_term_get_type(getTerm(f1));
    long f2Type = msat_term_get_type(getTerm(f2));

    // ite currently doesnt work with bool-types as branch arguments
    if (!msat_is_bool_type(msatEnv, f1Type) || !msat_is_bool_type(msatEnv, f2Type)) {
      t = msat_make_term_ite(msatEnv, getTerm(condition), getTerm(f1), getTerm(f2));
    } else {
      t =
          msat_make_and(msatEnv, msat_make_or(msatEnv, msat_make_not(msatEnv, getTerm(condition)), getTerm(f1)),
              msat_make_or(msatEnv, getTerm(condition), getTerm(f2)));
    }
    return encapsulate(t);
  }


  // ----------------- Uninterpreted functions -----------------

  /**
   * Declare an UF with a number of arguments.
   * All arguments and the return value of the UF have the same given type.
   * @return a declaration
   */
  private long declareUF(String name, long types, int argCount) {
    long[] tp = new long[argCount];
    Arrays.fill(tp, types);

    long funcType = msat_get_function_type(msatEnv, tp, tp.length, types);

    return msat_declare_function(msatEnv, name, funcType);
  }

  private long buildMsatUF(String name, long[] args, boolean predicate) {
    checkArgument(args.length > 0);
    long type = predicate ? msat_get_bool_type(msatEnv) : msatVarType;

    if (!useUIFs) {
      return buildMsatUfReplacement(type);
    }

    // only build a function when there actually are arguments
    if (args.length > 0) {
      long decl = declareUF(name, type, args.length);

      return buildMsatUF(decl, args);
    } else {
      long decl;
      type = msat_get_simple_type(msatEnv, name);
      decl = msat_declare_function(msatEnv, name, type);

      return msat_make_constant(msatEnv, decl);
    }

  }

  /**
   * Replacement for msat_make_uif, never call that method directly!
   */
  protected long buildMsatUF(long func, long[] args) {
    if (useUIFs) {
      return msat_make_uf(msatEnv, func, args);

    } else {
      return buildMsatUfReplacement(msatVarType);
    }
  }

  private long buildMsatUfReplacement(long type) {
    // just create a fresh variable
    String var = makeName(UIF_VARIABLE, ++uifVariableCounter);
    long decl = msat_declare_function(msatEnv, var, msatVarType);

    long t = msat_make_constant(msatEnv, decl);
    return t;
  }

  @Override
  public Formula makeUIP(String name, FormulaList args) {
    return encapsulate(buildMsatUF(name, getTerm(args), true));
  }

  @Override
  public Formula makeUIF(String name, FormulaList args) {
    return encapsulate(buildMsatUF(name, getTerm(args), false));
  }

  @Override
  public Formula makeUIF(String name, FormulaList args, int idx) {
    return encapsulate(buildMsatUF(makeName(name, idx), getTerm(args), false));
  }

  // ----------------- Other formulas -----------------

  @Override
  public Formula makeString(int i) {
    long n = msat_make_number(msatEnv, Integer.toString(i));
    return encapsulate(buildMsatUF(stringLitUfDecl, new long[] { n }));
  }

  private long buildMsatVariable(String var, long type) {
    long decl = msat_declare_function(msatEnv, var, type);

    long t = msat_make_constant(msatEnv, decl);
    return t;
  }

  @Override
  public Formula makeVariable(String var, int idx) {
    return makeVariable(makeName(var, idx));
  }

  @Override
  public Formula makeVariable(String var) {
    return encapsulate(buildMsatVariable(var, msatVarType));
  }

  @Override
  public Formula makePredicateVariable(String var, int idx) {
    String name = makeName("PRED" + var, idx);

    long bool_type = msat_get_bool_type(msatEnv);

    long decl = msat_declare_function(msatEnv, name, bool_type);
    long t = msat_make_constant(msatEnv, decl);
    return encapsulate(t);
  }

  @Override
  public Formula makeAssignment(Formula f1, Formula f2) {
    return makeEqual(f1, f2);
  }


  // ----------------- Convert to list -----------------

  @Override
  public FormulaList makeList(Formula pF) {
    return new Mathsat5FormulaList(getTerm(pF));
  }

  @Override
  public FormulaList makeList(Formula pF1, Formula pF2) {
    return new Mathsat5FormulaList(getTerm(pF1), getTerm(pF2));
  }

  @Override
  public FormulaList makeList(List<Formula> pFs) {
    long[] t = new long[pFs.size()];
    for (int i = 0; i < t.length; i++) {
      t[i] = getTerm(pFs.get(i));
    }
    return encapsulate(t);
  }

  // ----------------- Complex formula manipulation -----------------

  @Override
  public Formula createPredicateVariable(Formula atom) {
    long t = getTerm(atom);

    String repr = msat_term_is_atom(msatEnv, t)
        ? msat_term_repr(t) : ("#" + msat_term_id(t));

    long bool_type = msat_get_bool_type(msatEnv);
    long d = msat_declare_function(msatEnv, "\"PRED" + repr + "\"", bool_type);
    long var = msat_make_constant(msatEnv, d);
    return encapsulate(var);
  }

  @Override
  public String dumpFormula(Formula f) {
    return msat_to_smtlib2(msatEnv, getTerm(f));
  }

  /* Method for converting MSAT format to NUSMV format.
    public String printNusmvFormat(Formula f, Set<Formula> preds) {

      StringBuilder out = new StringBuilder();
      out.append("MODULE main\n");
      String repr = dumpFormula(f);
      for (String line : repr.split("\n")) {
        if (line.startsWith("VAR")) {
          out.append(line + ";\n");
        } else if (line.startsWith("DEFINE")) {
          String[] bits = line.split(" +", 5);
          out.append("DEFINE " + bits[1] + " " + bits[4] + ";\n");
        } else if (line.startsWith("FORMULA")) {
          out.append("INIT" + line.substring(7) + "\n");
        } else {
          out.append(line);
          out.append('\n');
        }
      }
      out.append("\nTRANS FALSE\n");
      out.append("INVARSPEC (0 = 0)\n");
      for (Formula p : preds) {
        repr = p.toString();
        repr = repr.replaceAll("([a-zA-Z:_0-9]+@[0-9]+)", "\"$1\"");
        out.append("PRED " + repr + "\n");
      }
      return out.toString();
    }
  */

  @Override
  public String dumpFormulaList(FormulaList pFlist) {
    assert pFlist instanceof NamedTermsWrapper;
    NamedTermsWrapper ntw = (NamedTermsWrapper) pFlist;
    return msat_named_list_to_smtlib2(msatEnv, ntw);
  }

  @Override
  public Formula parseInfix(String s) {
    long f = msat_from_string(msatEnv, s);
    return encapsulate(f);
  }

  @Override
  public Formula parse(String s) {
    long f = msat_from_smtlib2(msatEnv, s);
    return encapsulate(f);
  }

  @Override
  public FormulaList parseList(String pS) throws IllegalArgumentException {
    NamedTermsWrapper ntw = msat_named_list_from_smtlib2(msatEnv, pS);
    ntw.msatEnv = msatEnv;
    return ntw;
  }

  @Override
  public boolean isPurelyConjunctive(Formula f) {
    long t = getTerm(f);

    if (msat_term_is_atom(msatEnv, t)
        || msat_term_is_uf(msatEnv, t)) {
      // term is atom
      return true;

    } else if (msat_term_is_not(msatEnv, t)) {
      t = msat_term_get_arg(t, 0);
      return (msat_term_is_uf(msatEnv, t)
          || msat_term_is_atom(msatEnv, t));

    } else if (msat_term_is_and(msatEnv, t)) {
      int arity = msat_term_arity(t);
      for (int i = 0; i < arity; ++i) {
        if (!isPurelyConjunctive(encapsulate(msat_term_get_arg(t, i)))) {
          return false;
        }
      }
      return true;

    } else {
      return false;
    }
  }

  @Override
  public Formula instantiate(Formula f, SSAMap ssa) {
    Deque<Formula> toProcess = new ArrayDeque<Formula>();
    Map<Formula, Formula> cache = new HashMap<Formula, Formula>();

    toProcess.push(f);
    while (!toProcess.isEmpty()) {
      final Formula tt = toProcess.peek();
      if (cache.containsKey(tt)) {
        toProcess.pop();
        continue;
      }
      final long t = getTerm(tt);

      if (msat_term_is_constant(msatEnv, t)) {
        toProcess.pop();
        String name = msat_term_repr(t);
        int idx = ssa.getIndex(name);
        if (idx > 0) {
          // ok, the variable has an instance in the SSA, replace it
          long newt = buildMsatVariable(makeName(name, idx), msat_term_get_type(t));
          cache.put(tt, encapsulate(newt));
        } else {
          // the variable is not used in the SSA, keep it as is
          cache.put(tt, tt);
        }

      } else {
        boolean childrenDone = true;
        long[] newargs = new long[msat_term_arity(t)];
        for (int i = 0; i < newargs.length; ++i) {
          Formula c = encapsulate(msat_term_get_arg(t, i));
          Formula newC = cache.get(c);
          if (newC != null) {
            newargs[i] = getTerm(newC);
          } else {
            toProcess.push(c);
            childrenDone = false;
          }
        }

        if (childrenDone) {
          toProcess.pop();
          long newt;

          if (msat_term_is_uf(msatEnv, t)) {
            String name = msat_decl_get_name(msat_term_get_decl(t));
            assert name != null;

            if (ufCanBeLvalue(name)) {
              int idx = ssa.getIndex(name, encapsulate(newargs));
              if (idx > 0) {
                // ok, the variable has an instance in the SSA, replace it
                newt = buildMsatUF(makeName(name, idx), newargs, false);
              } else {
                long tDecl = msat_term_get_decl(t);
                newt = msat_make_term(msatEnv, tDecl, newargs);
              }
            } else {
              long tDecl = msat_term_get_decl(t);
              newt = msat_make_term(msatEnv, tDecl, newargs);

            }
          } else {

            long tDecl = msat_term_get_decl(t);
            if (newargs.length > 0) {
              newt = msat_make_term(msatEnv, tDecl, newargs);
            } else {
              newt = msat_make_constant(msatEnv, tDecl);
            }
          }

          cache.put(tt, encapsulate(newt));
        }
      }
    }

    Formula result = cache.get(f);
    assert result != null;
    return result;
  }

  private boolean ufCanBeLvalue(String name) {
    return name.startsWith(".{") || name.startsWith("->{");
  }

  @Override
  public Formula uninstantiate(Formula f) {
    Map<Formula, Formula> cache = uninstantiateCache;
    Deque<Formula> toProcess = new ArrayDeque<Formula>();

    toProcess.push(f);
    while (!toProcess.isEmpty()) {
      final Formula tt = toProcess.peek();
      if (cache.containsKey(tt)) {
        toProcess.pop();
        continue;
      }
      final long t = getTerm(tt);

      if (msat_term_is_constant(msatEnv, t)) {
        String name = parseName(msat_term_repr(t)).getFirst();

        long newt = buildMsatVariable(name, msat_term_get_type(t));
        cache.put(tt, encapsulate(newt));

      } else {
        boolean childrenDone = true;
        long[] newargs = new long[msat_term_arity(t)];
        for (int i = 0; i < newargs.length; ++i) {
          Formula c = encapsulate(msat_term_get_arg(t, i));
          Formula newC = cache.get(c);
          if (newC != null) {
            newargs[i] = getTerm(newC);
          } else {
            toProcess.push(c);
            childrenDone = false;
          }
        }

        if (childrenDone) {
          toProcess.pop();
          long newt;
          if (msat_term_is_uf(msatEnv, t)) {
            String name = msat_decl_get_name(msat_term_get_decl(t));
            assert name != null;

            if (ufCanBeLvalue(name)) {
              name = parseName(name).getFirst();

              newt = buildMsatUF(name, newargs, false);
            } else {
              long tDecl = msat_term_get_decl(t);
              newt = msat_make_term(msatEnv, tDecl, newargs);
            }
          } else {
            long tDecl = msat_term_get_decl(t);
            newt = msat_make_term(msatEnv, tDecl, newargs);
          }

          cache.put(tt, encapsulate(newt));
        }
      }
    }

    Formula result = cache.get(f);
    assert result != null;
    return result;
  }

  @Override
  public Collection<Formula> extractAtoms(Formula f,
      boolean splitArithEqualities, boolean conjunctionsOnly) {
    Set<Formula> handled = new HashSet<Formula>();
    List<Formula> atoms = new ArrayList<Formula>();

    Deque<Formula> toProcess = new ArrayDeque<Formula>();
    toProcess.push(f);
    handled.add(f);

    while (!toProcess.isEmpty()) {
      Formula tt = toProcess.pop();
      long t = getTerm(tt);
      assert handled.contains(tt);

      if (msat_term_is_true(msatEnv, t) || msat_term_is_false(msatEnv, t)) {
        continue;
      }

      if (msat_term_is_atom(msatEnv, t)) {
        tt = uninstantiate(tt);
        t = getTerm(tt);

        if (splitArithEqualities
            && msat_term_is_equal(msatEnv, t)
            && isPurelyArithmetic(tt)) {
          long a1 = msat_term_get_arg(t, 0);
          long a2 = msat_term_get_arg(t, 1);
          long t1 = msat_make_leq(msatEnv, a1, a2);
          //long t2 = msat_make_leq(msatEnv, a2, a1);
          Formula tt1 = encapsulate(t1);
          //SymbolicFormula tt2 = encapsulate(t2);
          handled.add(tt1);
          //cache.add(tt2);
          atoms.add(tt1);
          //atoms.add(tt2);
          atoms.add(tt);
        } else {
          atoms.add(tt);
        }

      } else if (conjunctionsOnly
          && !(msat_term_is_not(msatEnv, t) || msat_term_is_and(msatEnv, t))) {
        // conjunctions only, but formula is neither "not" nor "and"
        // treat this as atomic
        atoms.add(uninstantiate(tt));

      } else {
        // ok, go into this formula
        for (int i = 0; i < msat_term_arity(t); ++i) {
          long newt = msat_term_get_arg(t, i);
          Formula c = encapsulate(newt);
          if (handled.add(c)) {
            toProcess.push(c);
          }
        }
      }
    }

    return atoms;
  }

  @Override
  public Set<String> extractVariables(Formula f) {
    Set<Formula> seen = new HashSet<Formula>();
    Set<String> vars = new HashSet<String>();

    Deque<Formula> toProcess = new ArrayDeque<Formula>();
    toProcess.push(f);

    while (!toProcess.isEmpty()) {
      long t = getTerm(toProcess.pop());

      if (msat_term_is_true(msatEnv, t) || msat_term_is_false(msatEnv, t)) {
        continue;
      }

      if (msat_term_is_constant(msatEnv, t)) {
        vars.add(msat_term_repr(t));

      } else {
        // ok, go into this formula
        for (int i = 0; i < msat_term_arity(t); ++i) {
          long newt = msat_term_get_arg(t, i);
          Formula c = encapsulate(newt);

          if (seen.add(c)) {
            toProcess.push(c);
          }
        }
      }
    }

    return vars;
  }

  // returns true if the given term is a pure arithmetic term
  private boolean isPurelyArithmetic(Formula f) {
    Boolean result = arithCache.get(f);
    if (result != null) { return result; }

    long t = getTerm(f);

    boolean res = true;
    if (msat_term_is_uf(msatEnv, t)) {
      res = false;

    } else {
      int arity = msat_term_arity(t);
      for (int i = 0; i < arity; ++i) {
        res |= isPurelyArithmetic(encapsulate(msat_term_get_arg(t, i)));
        if (!res) {
          break;
        }
      }
    }
    arithCache.put(f, res);
    return res;
  }

  @Override
  public boolean checkSyntacticEntails(Formula leftFormula, Formula rightFormula) {
    final long leftTerm = getTerm(leftFormula);

    Deque<Long> toProcess = new ArrayDeque<Long>();
    Set<Long> seen = new HashSet<Long>();

    toProcess.push(getTerm(rightFormula));
    while (!toProcess.isEmpty()) {
      final long rightSubTerm = toProcess.pop();

      if (rightSubTerm == leftTerm) { return true; }

      if (!msat_term_is_constant(msatEnv, rightSubTerm)) {
        int args = msat_term_arity(rightSubTerm);
        for (int i = 0; i < args; ++i) {
          long arg = msat_term_get_arg(rightSubTerm, i);
          if (!seen.contains(arg)) {
            toProcess.add(arg);
            seen.add(arg);
          }
        }
      }
    }

    return false;
  }

  @Override
  public Formula[] getArguments(Formula f) {
    final long t = getTerm(f);
    int arity = msat_term_arity(t);
    Formula[] result = new Formula[arity];
    for (int i = 0; i < arity; ++i) {
      result[i] = encapsulate(msat_term_get_arg(t, i));
    }
    return result;
  }

  @Override
  public void declareUIP(String name, int argCount) {
    declareUF(name, msat_get_bool_type(msatEnv), argCount);
  }

  @Override
  public String getVersion() {
    return msat_get_version();
  }
}
