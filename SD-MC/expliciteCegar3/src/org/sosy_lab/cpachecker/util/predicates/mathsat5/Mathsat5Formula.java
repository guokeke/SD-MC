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

import static org.sosy_lab.cpachecker.util.predicates.mathsat5.Mathsat5NativeApi.*;

import java.io.File;
import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Map;

import org.sosy_lab.common.Files;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaList;
import org.sosy_lab.cpachecker.util.predicates.mathsat5.Mathsat5NativeApi.NamedTermsWrapper;


/**
 * A Formula represented as a MathSAT term.
 */
class Mathsat5Formula implements Formula, Serializable {

  private static final long serialVersionUID = 7662624283533815801L;
  private final long msatTerm;
  private final long msatEnv;

  public Mathsat5Formula(long e, long t) {
    assert e != 0;
    assert t != 0;

    msatTerm = t;
    msatEnv = e;
  }


  public long getTermEnv() {
    return msatEnv;
  }

  @Override
  public boolean isFalse() {
    return msat_term_is_false(msatEnv, msatTerm);
  }

  @Override
  public boolean isTrue() {
    return msat_term_is_true(msatEnv, msatTerm);
  }

  @Override
  public String toString() {
    return msat_term_repr(msatTerm);
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof Mathsat5Formula)) { return false; }
    return msatTerm == ((Mathsat5Formula) o).msatTerm;
  }

  long getTerm() {
    return msatTerm;
  }

  @Override
  public int hashCode() {
    return (int) msatTerm;
  }

  private Object writeReplace() throws ObjectStreamException {
    return new SerialProxy(this);
  }

  private static class SerialProxy implements Serializable {

    private static final long serialVersionUID = 6889568471468710163L;
    private transient static int storageIndex = -1;

    public SerialProxy(Formula pFormula) {
      if (storageIndex == -1) {
        storageIndex = GlobalInfo.getInstance().addHelperStorage(new MathsatFormulaStorage());
      }
      ((MathsatFormulaStorage) GlobalInfo.getInstance().getHelperStorage(storageIndex)).storeFormula(pFormula);
    }

    private void writeObject(java.io.ObjectOutputStream out) throws IOException {
      out.defaultWriteObject();
      out.writeInt(storageIndex);
    }

    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
      in.defaultReadObject();
      storageIndex = in.readInt();
    }

    private Object readResolve() throws ObjectStreamException {
      return ((MathsatFormulaStorage) GlobalInfo.getInstance().getHelperStorage(storageIndex)).restoreFormula();
    }
  }

  private static class MathsatFormulaStorage implements Serializable {

    private static final long serialVersionUID = -3773448463181606622L;
    private transient ArrayList<Formula> formulaeStorage;

    public MathsatFormulaStorage() {
      formulaeStorage = new ArrayList<Formula>();
    }

    public void storeFormula(Formula f) {
      formulaeStorage.add(f);
    }

    public Formula restoreFormula() {
      Formula result = formulaeStorage.get(0);
      formulaeStorage.remove(0);

      return result;
    }

    private void writeObject(java.io.ObjectOutputStream out) throws IOException {
      out.defaultWriteObject();

      long[] terms = new long[formulaeStorage.size()];
      String[] names = new String[formulaeStorage.size()];
      for (int i = 0; i < formulaeStorage.size(); i++) {
        terms[i] = ((Mathsat5Formula) formulaeStorage.get(i)).msatTerm;
        names[i] = "a" + i;
      }
      FormulaList flist = new NamedTermsWrapper(terms, names);

      String storageFormulaRepresentation = GlobalInfo.getInstance().getFormulaManager().dumpFormulaList(flist);

      //write everything
      out.writeInt(formulaeStorage.size());
      out.writeObject(storageFormulaRepresentation);
    }

    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
      in.defaultReadObject();

      int storageSize = in.readInt();
      String data = (String) in.readObject();
      Files.writeFile(new File("/tmp/error"), data);

      FormulaList storageFormula = GlobalInfo.getInstance().getFormulaManager().parseList(data);

      assert storageFormula instanceof NamedTermsWrapper;
      NamedTermsWrapper ntw = (NamedTermsWrapper) storageFormula;

      formulaeStorage = new ArrayList<Formula>(storageSize);
      Map<String, Long> termsMap = ntw.getTermsMap();
      for (int i = 0; i < storageSize; i++) {
        Long term = termsMap.get("a" + i);
        if (term == null)
          throw new RuntimeException(i + " is not in there");
        Formula f = new Mathsat5Formula(ntw.msatEnv, term);
        formulaeStorage.add(f);
      }
    }
  }
}
