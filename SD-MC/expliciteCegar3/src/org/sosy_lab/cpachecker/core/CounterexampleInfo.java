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
package org.sosy_lab.cpachecker.core;

import static com.google.common.base.Preconditions.*;

import java.io.File;
import java.util.Collection;
import java.util.Collections;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.arg.Path;
import org.xidian.cpachecker.dz.Proposition;

import com.google.common.collect.Lists;

public class CounterexampleInfo {

  private final boolean spurious;

  private final Path targetPath;
  private final Object assignment;

  // list with additional information about the counterexample
  private final Collection<Pair<Object, File>> furtherInfo;
  private static final CounterexampleInfo SPURIOUS = new CounterexampleInfo(true, null, null);
  private static final CounterexampleInfo UNSPURIOUS = new CounterexampleInfo(false, null, null);
  private Pair<AbstractState,Precision> toState;
  private Proposition proposition=null;
  private CounterexampleInfo(boolean pSpurious, Path pTargetPath, Object pAssignment) {
    spurious = pSpurious;
    targetPath = pTargetPath;
    assignment = pAssignment;

    if (!spurious) {
      furtherInfo = Lists.newArrayListWithExpectedSize(1);
    } else {
      furtherInfo = null;
    }
  }


  public Proposition getProposition() {
    return proposition;
  }


  public void setProposition(Proposition pProposition) {
    proposition = pProposition;
  }

  public static CounterexampleInfo spurious() {
    return SPURIOUS;
  }
  public static CounterexampleInfo unSpurious() {
    return UNSPURIOUS;
  }
  public static CounterexampleInfo feasible(Path pTargetPath, Object pAssignment) {
    return new CounterexampleInfo(false, pTargetPath, pAssignment);
  }

  public boolean isSpurious() {
    return spurious;
  }

  public Path getTargetPath() {
    checkState(!spurious);

    return targetPath;
  }

  public Object getTargetPathAssignment() {
    checkState(!spurious);

    return assignment;
  }

  /**
   * Add some additional information about the counterexample.
   *
   * @param info The information.
   * @param dumpFile The file where "info.toString()" should be dumped (may be null).
   */
  public void addFurtherInformation(Object info, File dumpFile) {
    checkState(!spurious);

    furtherInfo.add(Pair.of(checkNotNull(info), dumpFile));
  }

  /**
   * Get all additional information stored in this object.
   * A file where to dump it may be associated with each object, but this part
   * of the pair may be null.
   *
   * @return
   */
  public Collection<Pair<Object, File>> getAllFurtherInformation() {
    checkState(!spurious);

    return Collections.unmodifiableCollection(furtherInfo);
  }
}
