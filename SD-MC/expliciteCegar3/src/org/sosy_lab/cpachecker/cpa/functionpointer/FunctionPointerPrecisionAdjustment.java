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
package org.sosy_lab.cpachecker.cpa.functionpointer;

import org.sosy_lab.common.Triple;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSetView;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.exceptions.CPAException;

import com.google.common.base.Functions;
import com.google.common.base.Preconditions;

class FunctionPointerPrecisionAdjustment implements PrecisionAdjustment {

  private final PrecisionAdjustment wrappedPrecAdjustment;

  public FunctionPointerPrecisionAdjustment(PrecisionAdjustment pWrappedPrecAdjustment) {
    wrappedPrecAdjustment = pWrappedPrecAdjustment;
  }

  @Override
  public Triple<AbstractState, Precision, Action> prec(AbstractState pElement,
      Precision oldPrecision, UnmodifiableReachedSet pElements) throws CPAException {

    Preconditions.checkArgument(pElement instanceof FunctionPointerState);
    FunctionPointerState element = (FunctionPointerState)pElement;

    UnmodifiableReachedSet elements = new UnmodifiableReachedSetView(
        pElements,  ARGState.getUnwrapFunction(), Functions.<Precision>identity());

    AbstractState oldElement = element.getWrappedState();
   // System.out.println("Fun->wrappedPrecAdjustment=>"+wrappedPrecAdjustment.getClass().toString());
    Triple<AbstractState, Precision, Action> unwrappedResult = wrappedPrecAdjustment.prec(oldElement, oldPrecision, elements);

    AbstractState newElement = unwrappedResult.getFirst();
    Precision newPrecision = unwrappedResult.getSecond();
    Action action = unwrappedResult.getThird();

    if ((oldElement == newElement) && (oldPrecision == newPrecision)) {
      // nothing has changed
      return Triple.of(pElement, oldPrecision, action);
    }

    AbstractState resultElement = element.createDuplicateWithNewWrappedState(newElement);

    return Triple.of(resultElement, newPrecision, action);
  }
}
